#!/usr/bin/env python3
"""
RSSpanel feed core - pure-Python logic for scanning an audio folder and
building a podcast-compliant RSS 2.0 feed. No GTK dependencies, so it can be
tested and used from the command line:

    python3 feed_core.py "/path/to/folder"
"""

import json
import math
import os
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import time
import wave
from dataclasses import dataclass, field
from datetime import datetime, timezone
from email.utils import format_datetime
from pathlib import Path
from typing import Dict, List, Optional
from urllib.parse import quote, urlparse
from xml.sax.saxutils import escape

try:
    from tinytag import TinyTag  # optional: titles/durations from tags
except ImportError:  # pragma: no cover - depends on environment
    TinyTag = None

CONFIG_NAME = ".rsspanel.json"

MIME_TYPES = {
    ".mp4": "video/mp4",
    ".m4v": "video/x-m4v",
    ".mov": "video/quicktime",
    ".mp3": "audio/mpeg",
    ".m4a": "audio/mp4",
    ".aac": "audio/aac",
    ".wav": "audio/wav",
    ".flac": "audio/flac",
    ".ogg": "audio/ogg",
    ".opus": "audio/ogg",
}

VIDEO_EXTS = {".mp4", ".m4v", ".mov"}

# When several files share a name (e.g. "Song.wav" and "Song.mp3"), the feed
# uses the most podcast-friendly one in this order.
FORMAT_PREFERENCE = [".mp4", ".m4v", ".mov", ".mp3", ".m4a", ".aac", ".ogg", ".opus", ".flac", ".wav"]

DEFAULT_CONFIG = {
    "base_url": "https://yourdomain.com/podcast",
    "title": "",
    "description": "My personal daily streaming podcast feed.",
    "author": "",
    "language": "en-us",
    "image_url": "",
    "category": "Music",
    "explicit": False,
    "output_name": "feed.xml",
    "mp3_bitrate": "192k",
    "auto_generate": True,
    "publish_command": "",
    "github_repo": "",          # "owner/repo" once GitHub hosting is set up
    "github_release_tag": "episodes",
    # filename -> {"title", "description", "url" (hosted media URL), "pub" (epoch)}
    "tracks": {},
}


@dataclass
class Track:
    path: Path
    title: str
    description: str
    duration: Optional[float]
    size: int
    mtime: float
    mime: str
    alternates: List[Path] = field(default_factory=list)
    url: str = ""  # hosted URL override (e.g. GitHub Release asset)

    @property
    def name(self) -> str:
        return self.path.name

    @property
    def is_video(self) -> bool:
        return self.path.suffix.lower() in VIDEO_EXTS


# ----------------------------------------------------------------------------
# Security & Integrity Helpers
# ----------------------------------------------------------------------------
_XML_ILLEGAL_CTRL_RE = re.compile(r"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]")
_GITHUB_REPO_RE = re.compile(r"^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$")
_GITHUB_TAG_RE = re.compile(r"^[A-Za-z0-9_.-]{1,64}$")
_BITRATE_RE = re.compile(r"^\d{2,3}[kKmM]$")
_ATTR_ENTITIES = {'"': "&quot;", "'": "&#39;"}


def _xml_escape(value: object) -> str:
    """Escape text for XML/HTML element bodies after stripping illegal XML 1.0 control chars."""
    cleaned = _XML_ILLEGAL_CTRL_RE.sub("", str(value or ""))
    return escape(cleaned)


def _attr_escape(value: object) -> str:
    """Escape text for double- or single-quoted XML/HTML attributes."""
    cleaned = _XML_ILLEGAL_CTRL_RE.sub("", str(value or ""))
    return escape(cleaned, _ATTR_ENTITIES)


def sanitize_public_url(url: str) -> str:
    """Allow http://, https://, or relative paths; reject javascript:, data:, file:, or control chars."""
    raw = _XML_ILLEGAL_CTRL_RE.sub("", (url or "").strip())
    if not raw:
        return ""
    parsed = urlparse(raw)
    if parsed.scheme:
        if parsed.scheme.lower() not in ("http", "https"):
            return ""
        if not parsed.netloc:
            return ""
    return raw


def sanitize_output_name(output_name: str) -> str:
    """Validate feed output filename to prevent path traversal outside the feed folder."""
    name = (output_name or "feed.xml").strip()
    if (
        not name
        or "\x00" in name
        or "/" in name
        or "\\" in name
        or ".." in name
        or name.startswith(".")
        or name.startswith("-")
    ):
        raise ValueError(f"Unsafe feed output_name: {output_name!r}")
    if not name.lower().endswith((".xml", ".rss")):
        raise ValueError(f"Feed output_name must end with .xml or .rss: {output_name!r}")
    return name


def validate_github_repo(repo: str) -> str:
    """Validate GitHub owner/repo identifier to prevent gh CLI flag injection."""
    cleaned = (repo or "").strip()
    if (
        not cleaned
        or "\x00" in cleaned
        or cleaned.startswith("-")
        or ".." in cleaned
        or not _GITHUB_REPO_RE.match(cleaned)
    ):
        raise ValueError(f"Invalid GitHub repository identifier: {repo!r}")
    return cleaned


def validate_github_tag(tag: str) -> str:
    """Validate GitHub Release tag to prevent gh CLI flag injection."""
    cleaned = (tag or "episodes").strip()
    if (
        not cleaned
        or "\x00" in cleaned
        or cleaned.startswith("-")
        or ".." in cleaned
        or not _GITHUB_TAG_RE.match(cleaned)
    ):
        raise ValueError(f"Invalid GitHub release tag: {tag!r}")
    return cleaned


def sanitize_bitrate(bitrate: str, default: str = "192k") -> str:
    """Validate MP3 bitrate string (e.g. '192k', '256k')."""
    cleaned = (bitrate or "").strip()
    if _BITRATE_RE.match(cleaned):
        return cleaned.lower()
    return default


def _atomic_write_text(target: Path, content: str) -> None:
    """Atomically write UTF-8 text to target using a sibling temporary file + os.replace."""
    target = Path(target)
    if "\x00" in str(target):
        raise ValueError("Null byte in target path.")
    existing_mode = None
    if target.exists():
        st = target.stat()
        if stat.S_ISDIR(st.st_mode):
            raise IsADirectoryError(f"Cannot overwrite directory: {target}")
        if not stat.S_ISREG(st.st_mode):
            raise ValueError(f"Refusing to overwrite non-regular file: {target}")
        existing_mode = stat.S_IMODE(st.st_mode) & 0o777

    parent = target.parent
    parent.mkdir(parents=True, exist_ok=True)
    fd, tmp_path = tempfile.mkstemp(prefix=f".{target.name}.", suffix=".tmp", dir=str(parent))
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            f.write(content)
        os.chmod(tmp_path, existing_mode if existing_mode is not None else 0o644)
        os.replace(tmp_path, str(target))
    except Exception:
        try:
            if os.path.exists(tmp_path):
                os.unlink(tmp_path)
        except OSError:
            pass
        raise


# ----------------------------------------------------------------------------
# Config
# ----------------------------------------------------------------------------
def load_config(folder: Path) -> Dict:
    folder = Path(folder)
    cfg = json.loads(json.dumps(DEFAULT_CONFIG))
    cfg["title"] = folder.name
    path = folder / CONFIG_NAME
    if not path.is_file():
        legacy_path = folder / ".rsspad.json"
        if legacy_path.is_file():
            path = legacy_path
    if path.is_file():
        try:
            st = path.stat()
            if stat.S_ISREG(st.st_mode) and st.st_size <= 10 * 1024 * 1024:
                data = json.loads(path.read_text(encoding="utf-8"))
                if isinstance(data, dict):
                    cfg.update(data)
        except (OSError, ValueError):
            pass
    if not isinstance(cfg.get("tracks"), dict):
        cfg["tracks"] = {}
    try:
        cfg["output_name"] = sanitize_output_name(str(cfg.get("output_name") or "feed.xml"))
    except ValueError:
        cfg["output_name"] = "feed.xml"
    return cfg


def save_config(folder: Path, cfg: Dict) -> None:
    path = Path(folder) / CONFIG_NAME
    _atomic_write_text(path, json.dumps(cfg, indent=2, sort_keys=True))


# ----------------------------------------------------------------------------
# Scanning
# ----------------------------------------------------------------------------
def read_title_and_duration(path: Path):
    title, duration = None, None
    try:
        st = Path(path).stat()
        if not stat.S_ISREG(st.st_mode):
            return None, None
    except OSError:
        return None, None

    abs_path = os.path.abspath(str(path))
    if TinyTag is not None:
        try:
            tag = TinyTag.get(abs_path)
            title = tag.title or None
            duration = tag.duration or None
        except Exception:
            pass
    if duration is None and Path(abs_path).suffix.lower() == ".wav":
        try:
            with wave.open(abs_path, "rb") as w:
                rate = w.getframerate()
                if rate:
                    duration = w.getnframes() / float(rate)
        except Exception:
            pass
    if duration is None and shutil.which("ffprobe"):
        try:
            out = subprocess.run(
                ["ffprobe", "-v", "error", "-show_entries", "format=duration",
                 "-of", "default=noprint_wrappers=1:nokey=1", "--", abs_path],
                capture_output=True, text=True, timeout=10, check=False)
            duration = float(out.stdout.strip()) if out.stdout.strip() else None
        except (OSError, ValueError, subprocess.SubprocessError):
            pass
    if duration is not None and (not math.isfinite(duration) or duration < 0):
        duration = None
    return title, duration


def scan_folder(folder: Path, cfg: Optional[Dict] = None) -> List[Track]:
    """Return feed tracks, newest first. Same-stem duplicates collapse to one.
    Scans media files in folder directly or inside dedicated subfolders (e.g. tracks/, media/)."""
    folder = Path(folder)
    cfg = cfg or load_config(folder)
    raw_overrides = cfg.get("tracks", {})
    overrides = raw_overrides if isinstance(raw_overrides, dict) else {}

    groups: Dict[str, List[Path]] = {}

    def consider_file(f: Path):
        try:
            if f.name.startswith(".") or f.suffix.lower() not in MIME_TYPES:
                return
            st = f.stat()
            if stat.S_ISREG(st.st_mode):
                groups.setdefault(f.stem, []).append(f)
        except OSError:
            return

    # 1. Check dedicated subfolders first (tracks/, media/, episodes/)
    for sub in ("tracks", "media", "episodes"):
        sub_dir = folder / sub
        if sub_dir.is_dir():
            try:
                for f in sorted(sub_dir.iterdir()):
                    consider_file(f)
            except OSError:
                pass

    # 2. Check the root folder
    try:
        for f in sorted(folder.iterdir()):
            consider_file(f)
    except OSError:
        pass

    tracks = []
    for files in groups.values():
        files.sort(key=lambda p: FORMAT_PREFERENCE.index(p.suffix.lower()))
        chosen = files[0]
        try:
            chosen_stat = chosen.stat()
            mtime = min(p.stat().st_mtime for p in files)
        except OSError:
            continue
        tag_title, duration = read_title_and_duration(chosen)
        rel_key = chosen.relative_to(folder).as_posix()
        raw_ov = overrides.get(chosen.name) or overrides.get(rel_key) or overrides.get(files[-1].name) or {}
        ov = raw_ov if isinstance(raw_ov, dict) else {}
        title = str(ov.get("title") or tag_title or chosen.stem)
        description = str(ov.get("description") or f"Daily track selection: {title}")
        # A recorded publish time keeps pubDate stable across machines/clones
        if ov.get("pub") is not None:
            try:
                cand_pub = float(ov["pub"])
                if math.isfinite(cand_pub) and 0 <= cand_pub <= 32503680000:
                    mtime = cand_pub
            except (ValueError, TypeError):
                pass
        raw_url = str(ov.get("url") or "")
        safe_url = sanitize_public_url(raw_url)
        tracks.append(Track(
            path=chosen, title=title, description=description, duration=duration,
            size=chosen_stat.st_size, mtime=mtime,
            mime=MIME_TYPES[chosen.suffix.lower()], alternates=files[1:],
            url=safe_url))

    tracks.sort(key=lambda t: t.mtime, reverse=True)
    return tracks


# ----------------------------------------------------------------------------
# Feed generation
# ----------------------------------------------------------------------------
def fmt_duration(seconds: Optional[float]) -> str:
    if not seconds:
        return "--:--"
    s = int(round(seconds))
    h, m, s = s // 3600, (s % 3600) // 60, s % 60
    return f"{h:02d}:{m:02d}:{s:02d}" if h else f"{m:02d}:{s:02d}"


def fmt_size(num: int) -> str:
    for unit in ("B", "KB", "MB", "GB"):
        if num < 1024 or unit == "GB":
            return f"{num:.0f} {unit}" if unit == "B" else f"{num:.1f} {unit}"
        num /= 1024.0
    return f"{num} B"


def _rfc2822(ts: float) -> str:
    return format_datetime(datetime.fromtimestamp(ts, tz=timezone.utc), usegmt=True)


def build_feed_xml(cfg: Dict, tracks: List[Track], folder: Optional[Path] = None) -> str:
    base = sanitize_public_url(cfg.get("base_url", "")).rstrip("/")
    title = cfg.get("title") or "Untitled Feed"
    x = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        '<rss version="2.0" xmlns:itunes="http://www.itunes.com/dtds/podcast-1.0.dtd">',
        "  <channel>",
        f"    <title>{_xml_escape(title)}</title>",
        f"    <link>{_xml_escape(base)}</link>",
        f"    <language>{_xml_escape(cfg.get('language') or 'en-us')}</language>",
        f"    <description>{_xml_escape(cfg.get('description') or title)}</description>",
        f"    <lastBuildDate>{_rfc2822(datetime.now(timezone.utc).timestamp())}</lastBuildDate>",
        "    <generator>RSSpanel</generator>",
    ]
    if cfg.get("author"):
        x.append(f"    <itunes:author>{_xml_escape(cfg['author'])}</itunes:author>")
    safe_img_url = sanitize_public_url(cfg.get("image_url") or "")
    if safe_img_url:
        img_attr = _attr_escape(safe_img_url)
        img_body = _xml_escape(safe_img_url)
        x.append(f'    <itunes:image href="{img_attr}" />')
        x += ["    <image>", f"      <url>{img_body}</url>",
              f"      <title>{_xml_escape(title)}</title>", f"      <link>{_xml_escape(base)}</link>",
              "    </image>"]
    if cfg.get("category"):
        x.append(f'    <itunes:category text="{_attr_escape(cfg["category"])}" />')
    x.append(f"    <itunes:explicit>{'true' if cfg.get('explicit') else 'false'}</itunes:explicit>")

    for t in tracks:
        raw_t_url = track_url(cfg, t, folder)
        url_attr = _attr_escape(raw_t_url)
        url_body = _xml_escape(raw_t_url)
        x += [
            "    <item>",
            f"      <title>{_xml_escape(t.title)}</title>",
            f"      <description>{_xml_escape(t.description)}</description>",
            f"      <pubDate>{_rfc2822(t.mtime)}</pubDate>",
            f'      <enclosure url="{url_attr}" length="{int(t.size)}" type="{_attr_escape(t.mime)}" />',
            f'      <guid isPermaLink="false">{url_body}</guid>',
        ]
        if t.duration:
            s = int(round(t.duration))
            x.append(f"      <itunes:duration>{s // 3600:02d}:{(s % 3600) // 60:02d}:{s % 60:02d}</itunes:duration>")
        x.append("    </item>")

    x += ["  </channel>", "</rss>", ""]
    return "\n".join(x)


def track_url(cfg: Dict, t: Track, folder: Optional[Path] = None) -> str:
    """Public URL of a track: hosted override (e.g. GitHub Release) or base_url/file."""
    if t.url:
        safe_override = sanitize_public_url(t.url)
        if safe_override:
            return safe_override
    base = sanitize_public_url(cfg.get("base_url", "")).rstrip("/")
    if folder:
        try:
            rel = t.path.relative_to(folder).as_posix()
            return f"{base}/{quote(rel)}" if base else quote(rel)
        except ValueError:
            pass
    return f"{base}/{quote(t.name)}" if base else quote(t.name)


def write_feed(folder: Path, cfg: Optional[Dict] = None) -> Path:
    folder = Path(folder).resolve()
    cfg = cfg or load_config(folder)
    out_name = sanitize_output_name(str(cfg.get("output_name") or "feed.xml"))
    tracks = scan_folder(folder, cfg)
    out = (folder / out_name).resolve()
    if out.parent != folder:
        raise ValueError(f"Output path escapes feed folder: {out}")
    _atomic_write_text(out, build_feed_xml(cfg, tracks, folder=folder))
    if cfg.get("github_repo"):
        _atomic_write_text(folder / "index.html", build_index_html(cfg, tracks, folder=folder))
    return out


def build_index_html(cfg: Dict, tracks: List[Track], folder: Optional[Path] = None) -> str:
    """A sleek neon landing page for GitHub Pages with responsive video previews."""
    title_text = cfg.get("title") or "Feed"
    title = _xml_escape(title_text)
    title_attr = _attr_escape(title_text)
    base = sanitize_public_url(cfg.get("base_url", "")).rstrip("/")
    out_name = sanitize_output_name(str(cfg.get("output_name") or "feed.xml"))
    feed = _attr_escape(f"{base}/{out_name}" if base else out_name)
    items = []
    for t in tracks:
        url = _attr_escape(track_url(cfg, t, folder))
        if t.is_video:
            poster_file = f"{t.path.stem}_poster.jpg"
            p_same = t.path.parent / poster_file
            p_root = (folder / poster_file) if folder else None
            if p_same.is_file():
                if folder:
                    try:
                        rel = p_same.relative_to(folder).as_posix()
                    except ValueError:
                        rel = p_same.name
                else:
                    rel = f"{t.path.parent.name}/{poster_file}" if t.path.parent.name in ("tracks", "media", "episodes") else poster_file
                poster_url = f"{base}/{quote(rel)}" if base else quote(rel)
            elif p_root and p_root.is_file():
                poster_url = f"{base}/{quote(poster_file)}" if base else quote(poster_file)
            else:
                rel = f"{t.path.parent.name}/{poster_file}" if t.path.parent.name in ("tracks", "media", "episodes") else poster_file
                poster_url = f"{base}/{quote(rel)}" if base else quote(rel)
            poster_attr = f' poster="{_attr_escape(poster_url)}"'
            player = (
                f'<video controls preload="metadata"{poster_attr}>\n'
                f'      <source src="{url}" type="video/mp4">\n'
                f'      <p><a href="{url}" class="download-link">Watch / Download {_xml_escape(t.name)}</a></p>\n'
                f'    </video>'
            )
        else:
            player = f'<audio controls preload="metadata" src="{url}"></audio>'
        items.append(
            f'  <article>\n'
            f'    <h2>{_xml_escape(t.title)}</h2>\n'
            f'    <p class="meta">{datetime.fromtimestamp(t.mtime).strftime("%B %d, %Y")}'
            f' &middot; {fmt_duration(t.duration)} &middot; {fmt_size(t.size)}</p>\n'
            f'    {player}\n'
            f'    <p class="desc">{_xml_escape(t.description)}</p>\n'
            f'  </article>'
        )
    return f"""<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>{title}</title>
  <link rel="alternate" type="application/rss+xml" title="{title_attr}" href="{feed}">
  <style>
    :root {{
      --bg: #0b0f19;
      --card-bg: #0d1322;
      --cyan: #00f0ff;
      --blue: #38bdf8;
      --border: rgba(0, 240, 255, 0.25);
    }}
    * {{ box-sizing: border-box; }}
    body {{
      background: var(--bg);
      color: #ffffff;
      font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif;
      margin: 0;
      padding: 24px 16px;
      line-height: 1.5;
    }}
    main {{ max-width: 760px; margin: 0 auto; }}
    header {{ margin-bottom: 24px; text-align: center; }}
    h1 {{ color: var(--cyan); margin: 0 0 6px 0; font-size: 1.8rem; }}
    .sub {{ color: var(--blue); margin: 0; font-size: 0.95rem; }}
    article {{
      background: var(--card-bg);
      border: 1px solid var(--border);
      border-radius: 10px;
      padding: 18px;
      margin: 20px 0;
      clear: both;
      box-shadow: 0 4px 12px rgba(0, 0, 0, 0.4);
    }}
    article h2 {{ margin: 0 0 4px 0; font-size: 1.25rem; color: #ffffff; }}
    .meta {{ color: var(--blue); font-size: 0.85rem; margin: 0 0 12px 0; }}
    video {{
      width: 100%;
      max-height: 75vh;
      border-radius: 8px;
      background: #000000;
      display: block;
      outline: none;
    }}
    audio {{ width: 100%; display: block; }}
    .desc {{ margin: 12px 0 0 0; color: #cbd5e1; font-size: 0.92rem; }}
    .download-link {{ color: var(--cyan); text-decoration: none; }}
    .download-link:hover {{ text-decoration: underline; }}
    footer {{
      margin-top: 36px;
      text-align: center;
      color: #64748b;
      font-size: 0.8rem;
    }}
  </style>
</head>
<body>
<main>
  <header>
    <h1>{title}</h1>
    <p class="sub">{escape(cfg.get('description') or '')}</p>
  </header>
  {''.join(items)}
  <footer>
    <p>Powered by RSSpanel</p>
  </footer>
</main>
</body>
</html>
"""


def make_cover_command(video: Path, out: Path, size: int = 1400) -> List[str]:
    """ffmpeg command: grab a frame and fit it on a square dark canvas."""
    if "\x00" in str(video) or "\x00" in str(out):
        raise ValueError("Null byte in ffmpeg file path.")
    safe_size = max(64, min(4096, int(size)))
    abs_video = os.path.abspath(str(video))
    abs_out = os.path.abspath(str(out))
    vf = (f"scale={safe_size}:{safe_size}:force_original_aspect_ratio=decrease,"
          f"pad={safe_size}:{safe_size}:(ow-iw)/2:(oh-ih)/2:color=0x0b0f19")
    return ["ffmpeg", "-hide_banner", "-loglevel", "error", "-y", "-ss", "5", "-i", abs_video,
            "-frames:v", "1", "-vf", vf, "-q:v", "3", abs_out]


def mp4_compress_command(src: Path, dst: Path, crf: int = 23) -> List[str]:
    """ffmpeg command: re-encode video to H.264/AAC with faststart for streaming."""
    if "\x00" in str(src) or "\x00" in str(dst):
        raise ValueError("Null byte in ffmpeg file path.")
    safe_crf = max(0, min(51, int(crf)))
    abs_src = os.path.abspath(str(src))
    abs_dst = os.path.abspath(str(dst))
    return ["ffmpeg", "-hide_banner", "-loglevel", "error", "-y", "-i", abs_src,
            "-c:v", "libx264", "-crf", str(safe_crf), "-preset", "medium",
            "-c:a", "aac", "-b:a", "160k", "-movflags", "+faststart", abs_dst]


def extract_mp3_command(src: Path, bitrate: str = "192k") -> List[str]:
    """ffmpeg command: extract/convert audio to MP3."""
    if "\x00" in str(src):
        raise ValueError("Null byte in ffmpeg file path.")
    src_path = Path(os.path.abspath(str(src)))
    dst_path = src_path.with_suffix(".mp3")
    safe_bitrate = sanitize_bitrate(bitrate)
    return ["ffmpeg", "-hide_banner", "-loglevel", "error", "-y", "-i", str(src_path),
            "-vn", "-codec:a", "libmp3lame", "-b:a", safe_bitrate,
            "-metadata", f"title={src_path.stem}", str(dst_path)]


# ----------------------------------------------------------------------------
# GitHub Hosting & Publishing (Pages + Releases for >100 MB media)
# ----------------------------------------------------------------------------
GITHUB_GIT_LIMIT = 95 * 1024 * 1024  # 95 MB threshold before using GitHub Releases


def sync_github(folder: Path, log_fn=print) -> bool:
    """
    Sync feed folder to GitHub:
    - Any media file > 95 MB (or all media if github_release_tag is set) is uploaded
      to a GitHub Release so it never hits GitHub's 100 MB git blob limit.
    - Each uploaded asset's browser_download_url is saved into .rsspanel.json track overrides.
    - Cover art is auto-generated from the first video if missing.
    - feed.xml and index.html are regenerated and committed + pushed to main.
    """
    folder = Path(folder).resolve()
    cfg = load_config(folder)
    raw_repo = (cfg.get("github_repo") or "").strip()
    raw_tag = (cfg.get("github_release_tag") or "episodes").strip()

    if not raw_repo:
        log_fn("No github_repo configured in .rsspanel.json")
        return False
    try:
        repo = validate_github_repo(raw_repo)
        tag = validate_github_tag(raw_tag)
    except ValueError as exc:
        log_fn(f"Invalid GitHub configuration: {exc}")
        return False

    tracks = scan_folder(folder, cfg)
    overrides = cfg.setdefault("tracks", {})

    # 1. Auto-generate cover.jpg from first video if missing, and poster frames for videos
    cover_path = folder / "cover.jpg"
    videos = [t.path for t in tracks if t.is_video]
    if shutil.which("ffmpeg"):
        if not cover_path.exists() and videos:
            log_fn(f"Generating cover.jpg from {videos[0].name}...")
            subprocess.run(make_cover_command(videos[0], cover_path), check=False)
        for v in videos:
            pframe = v.parent / f"{v.stem}_poster.jpg"
            if not pframe.exists():
                log_fn(f"Generating preview poster for {v.name}...")
                subprocess.run(
                    ["ffmpeg", "-hide_banner", "-loglevel", "error", "-y", "-ss", "3",
                     "-i", str(v), "-frames:v", "1", "-q:v", "3", str(pframe)],
                    check=False
                )
    if cover_path.exists() and not cfg.get("image_url"):
        base = (cfg.get("base_url") or "").rstrip("/")
        if base and "yourdomain.com" not in base:
            cfg["image_url"] = f"{base}/cover.jpg"

    # 2. Ensure GitHub Release exists and upload track assets via gh CLI
    if shutil.which("gh"):
        chk = subprocess.run(
            ["gh", "release", "view", tag, "--repo", repo, "--json", "assets"],
            cwd=str(folder), capture_output=True, text=True, check=False)
        if chk.returncode != 0:
            log_fn(f"Creating GitHub Release '{tag}' on {repo}...")
            subprocess.run(
                ["gh", "release", "create", tag, "--repo", repo,
                 "--title", f"{cfg.get('title') or 'Podcast'} Episodes",
                 "--notes", "Automated media asset hosting managed by RSSpanel."],
                cwd=str(folder), check=False)
            chk = subprocess.run(
                ["gh", "release", "view", tag, "--repo", repo, "--json", "assets"],
                cwd=str(folder), capture_output=True, text=True, check=False)

        existing_assets = {}
        if chk.returncode == 0 and chk.stdout.strip():
            try:
                data = json.loads(chk.stdout)
                for a in data.get("assets", []):
                    existing_assets[a["name"]] = (a.get("url") or "", a.get("size") or 0)
            except ValueError:
                pass

        for t in tracks:
            ov = overrides.setdefault(t.name, {})
            if not ov.get("pub"):
                ov["pub"] = t.mtime
            # Check if asset with matching name/safe-name or existing URL is already uploaded
            asset_url = f"https://github.com/{repo}/releases/download/{tag}/{quote(t.name)}"
            need_upload = True
            for aname, (aurl, asize) in existing_assets.items():
                if asize == t.size and (aname == t.name or aname == t.name.replace(" ", ".")):
                    ov["url"] = aurl
                    need_upload = False
                    break
            if need_upload:
                log_fn(f"Uploading {t.name} ({fmt_size(t.size)}) to GitHub Release '{tag}'...")
                max_retries = 3
                up_success = False
                for attempt in range(1, max_retries + 1):
                    up = subprocess.run(
                        ["gh", "release", "upload", tag, str(t.path), "--clobber", "--repo", repo],
                        cwd=str(folder), capture_output=True, text=True, check=False)
                    if up.returncode == 0:
                        up_success = True
                        break
                    log_fn(f"Upload attempt {attempt}/{max_retries} failed for {t.name}: {up.stderr.strip()}")
                    if attempt < max_retries:
                        time.sleep(2 * attempt)
                if not up_success:
                    log_fn(f"Upload permanently failed for {t.name}")
                    return False
                # Re-query release assets to get exact browser_download_url (gh normalizes spaces to dots)
                q = subprocess.run(
                    ["gh", "release", "view", tag, "--repo", repo, "--json", "assets"],
                    cwd=str(folder), capture_output=True, text=True, check=False)
                if q.returncode == 0:
                    try:
                        for a in json.loads(q.stdout).get("assets", []):
                            if a.get("size") == t.size and (
                                a["name"] == t.name or a["name"] == t.name.replace(" ", ".")
                            ):
                                asset_url = a["url"]
                                break
                    except ValueError:
                        pass
                ov["url"] = asset_url
                log_fn(f"Uploaded -> {ov['url']}")
                save_config(folder, cfg)

    # 3. Save updated config and regenerate feed.xml + index.html
    save_config(folder, cfg)
    out_feed = write_feed(folder, cfg)
    log_fn(f"Generated {out_feed.name} and index.html")

    # 4. Commit and push feed metadata & RSSpanel code to GitHub
    for cmd in (
        ["git", "add", "-A"],
        ["git", "commit", "-m", f"Update feed ({len(tracks)} episodes)"],
        ["git", "push", "-u", "origin", "main"],
    ):
        res = subprocess.run(cmd, cwd=str(folder), capture_output=True, text=True, check=False)
        if res.stdout.strip():
            log_fn(res.stdout.strip())
        if res.returncode != 0 and "nothing to commit" not in (res.stdout + res.stderr):
            if cmd[1] != "commit":
                log_fn(f"git {' '.join(cmd[1:])} warning: {res.stderr.strip()}")
    log_fn("GitHub sync complete!")
    return True


def wav_to_mp3_command(src: Path, bitrate: str = "192k") -> List[str]:
    if "\x00" in str(src):
        raise ValueError("Null byte in ffmpeg file path.")
    src_path = Path(os.path.abspath(str(src)))
    dst_path = src_path.with_suffix(".mp3")
    safe_bitrate = sanitize_bitrate(bitrate)
    return ["ffmpeg", "-hide_banner", "-loglevel", "error", "-y", "-i", str(src_path),
            "-codec:a", "libmp3lame", "-b:a", safe_bitrate,
            "-metadata", f"title={src_path.stem}", str(dst_path)]


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--sync-github":
        target = Path(sys.argv[2] if len(sys.argv) > 2 else ".").expanduser().resolve()
        ok = sync_github(target)
        sys.exit(0 if ok else 1)
    target = Path(sys.argv[1] if len(sys.argv) > 1 else ".").expanduser().resolve()
    path = write_feed(target)
    print(f"Wrote {path} ({len(scan_folder(target))} tracks)")
