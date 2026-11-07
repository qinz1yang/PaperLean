#!/usr/bin/env python3
"""
build_artifact.py: Download pre-built CI artifacts for a Lean commit.

Usage:
    build_artifact.py                     # Download artifact for current HEAD
    build_artifact.py --sha abc1234       # Download artifact for specific commit
    build_artifact.py --clear-cache       # Clear artifact cache

This script downloads pre-built binaries from GitHub Actions CI runs,
which is much faster than building from source (~30s vs 2-5min).

Artifacts are cached in ~/.cache/lean_build_artifact/ for reuse.
"""

import argparse
from contextlib import contextmanager
import hashlib
import re
import stat
import tempfile
import json
import os
import platform
import shutil
import subprocess
import sys
import urllib.request
import urllib.error
from pathlib import Path
from typing import Optional

# Constants
GITHUB_API_BASE = "https://api.github.com"
LEAN4_REPO = "leanprover/lean4"

# CI artifact cache
CACHE_DIR = Path.home() / '.cache' / 'lean_build_artifact'
ARTIFACT_CACHE = CACHE_DIR

# Sentinel value indicating CI failed (don't bother building locally)
CI_FAILED = object()

# ANSI colors for terminal output
class Colors:
    RED = '\033[91m'
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    BLUE = '\033[94m'
    BOLD = '\033[1m'
    RESET = '\033[0m'

def color(text: str, c: str) -> str:
    """Apply color to text if stdout is a tty."""
    if sys.stdout.isatty():
        return f"{c}{text}{Colors.RESET}"
    return text

def error(msg: str) -> None:
    """Print error message and exit."""
    print(color(f"Error: {msg}", Colors.RED), file=sys.stderr)
    sys.exit(1)

def warn(msg: str) -> None:
    """Print warning message."""
    print(color(f"Warning: {msg}", Colors.YELLOW), file=sys.stderr)

def info(msg: str) -> None:
    """Print info message."""
    print(color(msg, Colors.BLUE), file=sys.stderr)

def success(msg: str) -> None:
    """Print success message."""
    print(color(msg, Colors.GREEN), file=sys.stderr)

# -----------------------------------------------------------------------------
# Platform detection
# -----------------------------------------------------------------------------

def get_artifact_name() -> Optional[str]:
    """Get CI artifact name for current platform."""
    system = platform.system()
    machine = platform.machine()

    if system == 'Darwin':
        if machine == 'arm64':
            return 'build-macOS aarch64'
        if machine == 'x86_64':
            return 'build-macOS'
    elif system == 'Linux':
        if machine == 'aarch64':
            return 'build-Linux aarch64'
        if machine == 'x86_64':
            return 'build-Linux release'
    return None

# -----------------------------------------------------------------------------
# GitHub API helpers
# -----------------------------------------------------------------------------

_github_token_warning_shown = False

def get_github_token() -> Optional[str]:
    """Get GitHub token from environment or gh CLI."""
    global _github_token_warning_shown

    # Check environment variable first
    token = os.environ.get('GITHUB_TOKEN')
    if token:
        return token

    # Try to get token from gh CLI
    try:
        result = subprocess.run(
            ['gh', 'auth', 'token'],
            capture_output=True,
            text=True,
            timeout=5
        )
        if result.returncode == 0 and result.stdout.strip():
            return result.stdout.strip()
    except (FileNotFoundError, subprocess.TimeoutExpired):
        pass

    # Warn once if no token available
    if not _github_token_warning_shown:
        _github_token_warning_shown = True
        warn("No GitHub authentication found. API rate limits may apply.")
        warn("Run 'gh auth login' or set GITHUB_TOKEN to avoid rate limiting.")

    return None

def github_api_request(url: str) -> dict:
    """Make a GitHub API request and return JSON response."""
    headers = {
        'Accept': 'application/vnd.github.v3+json',
        'User-Agent': 'build-artifact'
    }

    token = get_github_token()
    if token:
        headers['Authorization'] = f'token {token}'

    req = urllib.request.Request(url, headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=30) as response:
            return json.loads(response.read().decode())
    except urllib.error.HTTPError as e:
        if e.code == 403:
            error(f"GitHub API rate limit exceeded. Set GITHUB_TOKEN environment variable to increase limit.")
        elif e.code == 404:
            error(f"GitHub resource not found: {url}")
        else:
            error(f"GitHub API error: {e.code} {e.reason}")
    except urllib.error.URLError as e:
        error(f"Network error accessing GitHub API: {e.reason}")

# -----------------------------------------------------------------------------
# CI artifact cache functions
# -----------------------------------------------------------------------------

CACHE_RECEIPT = '.complete.json'

def cache_identity(sha: str) -> dict:
    """Describe the complete source/platform identity, without abbreviated SHA keys."""
    if not re.fullmatch(r'[0-9a-fA-F]{40}', sha):
        raise ValueError('artifact cache requires a full 40-character commit SHA')
    return {
        'repository': LEAN4_REPO,
        'commit': sha.lower(),
        'artifact': get_artifact_name(),
        'system': platform.system(),
        'machine': platform.machine(),
    }

def get_cache_path(sha: str) -> Path:
    """Get a cache directory specific to the full commit, repository and platform."""
    identity = cache_identity(sha)
    key = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()
    return ARTIFACT_CACHE / f"{identity['commit']}-{key}"

def tree_inventory(root: Path) -> list:
    """Describe a relocatable payload. Record file identity as well as size and mode."""
    entries = []
    for path in sorted(root.rglob('*')):
        if path == root / CACHE_RECEIPT:
            continue
        entry = {'path': path.relative_to(root).as_posix()}
        metadata = path.lstat()
        if stat.S_ISLNK(metadata.st_mode):
            target = os.readlink(path)
            try:
                path.resolve().relative_to(root.resolve())
            except (ValueError, RuntimeError) as exc:
                raise ValueError(f'artifact link escapes its payload: {path}') from exc
            if os.path.isabs(target):
                raise ValueError(f'non-relocatable artifact link: {path}')
            entry.update(kind='symlink', target=target)
        elif stat.S_ISDIR(metadata.st_mode):
            entry.update(kind='directory')
        elif stat.S_ISREG(metadata.st_mode):
            entry.update(kind='file', size=metadata.st_size, mode=stat.S_IMODE(metadata.st_mode),
                         dev=metadata.st_dev, ino=metadata.st_ino, ctime_ns=metadata.st_ctime_ns,
                         mtime_ns=metadata.st_mtime_ns)
        else:
            raise ValueError(f'unsupported artifact entry: {path}')
        entries.append(entry)
    return entries

def has_toolchain_layout(root: Path) -> bool:
    """Require executables and the core import roots, not just an early-moved bin/lean."""
    executables = ('lean', 'lake', 'leanc')
    modules = ('Init.olean', 'Lean.olean', 'Lake.olean')
    return (all((root / 'bin' / name).is_file() and os.access(root / 'bin' / name, os.X_OK)
                for name in executables)
            and all((root / 'lib' / 'lean' / name).is_file() for name in modules))

def is_cached(sha: str) -> bool:
    """Accept only an atomically published, complete entry for this exact identity."""
    try:
        identity = cache_identity(sha)
        if identity['artifact'] is None:
            return False
        cache_path = get_cache_path(sha)
        if cache_path.is_symlink():
            return False
        fd = os.open(cache_path / CACHE_RECEIPT, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
        with os.fdopen(fd, 'rb') as handle:
            if not stat.S_ISREG(os.fstat(handle.fileno()).st_mode):
                return False
            receipt = json.load(handle)
        return (receipt.get('version') == 2 and receipt.get('identity') == identity
                and has_toolchain_layout(cache_path)
                and receipt.get('entries') == tree_inventory(cache_path))
    except (OSError, ValueError, TypeError, AttributeError):
        return False

@contextmanager
def cache_lock(path: Path, shared: bool = False):
    """Use advisory locks on supported artifact platforms (macOS and Linux)."""
    if os.name == 'nt':
        # Artifact downloads are unsupported here; retain --clear-cache for legacy entries.
        yield
        return
    import fcntl
    path.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(path, os.O_RDWR | os.O_CREAT | os.O_NONBLOCK | os.O_NOFOLLOW, 0o600)
    with os.fdopen(fd, 'rb') as handle:
        if not stat.S_ISREG(os.fstat(handle.fileno()).st_mode):
            raise ValueError(f'invalid cache lock: {path}')
        fcntl.flock(handle.fileno(), fcntl.LOCK_SH if shared else fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)

def maintenance_lock_path() -> Path:
    # Keep this inode outside the tree that --clear-cache removes.
    return ARTIFACT_CACHE.parent / f'.{ARTIFACT_CACHE.name}.lock'

def clear_cache() -> None:
    """Wait for active downloads before deleting cache entries and their key locks."""
    with cache_lock(maintenance_lock_path()):
        if ARTIFACT_CACHE.is_symlink():
            ARTIFACT_CACHE.unlink()
            info(f"Removed cache link at {ARTIFACT_CACHE}")
        elif ARTIFACT_CACHE.exists():
            shutil.rmtree(ARTIFACT_CACHE)
            info(f"Cleared cache at {ARTIFACT_CACHE}")
        else:
            info(f"Cache directory does not exist: {ARTIFACT_CACHE}")


def check_zstd_support() -> bool:
    """Check if tar supports zstd compression."""
    try:
        result = subprocess.run(
            ['tar', '--zstd', '--version'],
            capture_output=True,
            timeout=5
        )
        return result.returncode == 0
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return False

def check_gh_available() -> bool:
    """Check if gh CLI is available and authenticated."""
    try:
        result = subprocess.run(
            ['gh', 'auth', 'status'],
            capture_output=True,
            timeout=10
        )
        return result.returncode == 0
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return False

def download_ci_artifact(sha: str, quiet: bool = False):
    """Return a complete toolchain, CI_FAILED, or None for a local-build fallback."""
    if get_artifact_name() is None:
        return None
    try:
        cache_path = get_cache_path(sha)
        # A cache clear cannot remove the key-lock inode while a downloader owns it.
        with cache_lock(maintenance_lock_path(), shared=True):
            locks = ARTIFACT_CACHE / '.locks'
            locks.mkdir(parents=True, exist_ok=True)
            if not stat.S_ISDIR(locks.lstat().st_mode):
                return None
            with cache_lock(locks / (cache_path.name + '.lock')):
                if is_cached(sha):
                    return cache_path
                return download_ci_artifact_locked(sha, cache_path, quiet)
    except (OSError, ValueError, subprocess.TimeoutExpired):
        return None

def download_ci_artifact_locked(sha: str, cache_path: Path, quiet: bool):
    """Build privately under the key lock; only rename a fully validated directory."""
    identity = cache_identity(sha)
    artifact_name = identity['artifact']
    result = subprocess.run(
        ['gh', 'api', f'repos/{LEAN4_REPO}/actions/runs?head_sha={sha}&per_page=100',
         '--jq', r'.workflow_runs[] | select(.name == "CI") | "\(.id) \(.conclusion // "null")"'],
        capture_output=True, text=True, timeout=30)
    if result.returncode != 0 or not result.stdout.strip():
        return None
    parts = result.stdout.strip().splitlines()[0].split(' ', 1)
    run_id = parts[0]
    conclusion = parts[1] if len(parts) > 1 else 'null'
    if not run_id.isdigit():
        return None

    result = subprocess.run(
        ['gh', 'api', f'repos/{LEAN4_REPO}/actions/runs/{run_id}/artifacts',
         '--jq', f'.artifacts[] | select(.name == "{artifact_name}" and (.expired | not)) | .id'],
        capture_output=True, text=True, timeout=30)
    if result.returncode != 0 or not result.stdout.strip():
        return CI_FAILED if conclusion == 'failure' else None
    artifact_id = result.stdout.strip().splitlines()[0]
    if not artifact_id.isdigit():
        return None

    with tempfile.TemporaryDirectory(prefix=f'.{cache_path.name}.tmp-', dir=ARTIFACT_CACHE) as temp:
        temporary = Path(temp)
        download = temporary / 'download'
        extracted = temporary / 'extracted'
        download.mkdir()
        extracted.mkdir()
        if not quiet:
            print('downloading CI artifact... ', end='', flush=True)
        result = subprocess.run(
            ['gh', 'run', 'download', run_id, '-n', artifact_name, '-R', LEAN4_REPO, '-D', str(download)],
            capture_output=True, text=True, timeout=600)
        if result.returncode != 0:
            return None
        archives = list(download.glob('*.tar.zst'))
        if len(archives) != 1:
            return None
        archive = archives[0]
        digest = hashlib.sha256()
        with archive.open('rb') as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b''):
                digest.update(chunk)
        if not quiet:
            print('extracting... ', end='', flush=True)
        result = subprocess.run(
            ['tar', '--zstd', '-xf', str(archive)], cwd=extracted, capture_output=True, timeout=300)
        if result.returncode != 0:
            return None

        roots = list(extracted.iterdir())
        if len(roots) == 1 and roots[0].is_dir() and roots[0].name.startswith('lean-'):
            payload = roots[0]
        else:
            payload = extracted
        if payload.is_symlink() or not has_toolchain_layout(payload):
            return None
        receipt = {
            'version': 2,
            'identity': identity,
            'run_id': run_id,
            'artifact_id': artifact_id,
            'archive_sha256': digest.hexdigest(),
            'entries': tree_inventory(payload),
        }
        # The receipt belongs to the cache writer. An archive entry with this name is invalid,
        # including symlinks, hard links and special files.
        with (payload / CACHE_RECEIPT).open('x', encoding='utf-8') as handle:
            json.dump(receipt, handle, sort_keys=True)
            handle.write('\n')
        # Legacy/incomplete entries are misses. Do not touch them until a replacement is ready,
        # and never remove a published entry in an exception handler or another caller's temp.
        if cache_path.is_dir() and not cache_path.is_symlink():
            shutil.rmtree(cache_path)
        else:
            cache_path.unlink(missing_ok=True)
        os.replace(payload, cache_path)
        return cache_path


# -----------------------------------------------------------------------------
# Git helpers
# -----------------------------------------------------------------------------

def get_current_commit() -> str:
    """Get the current git HEAD commit SHA."""
    try:
        result = subprocess.run(
            ['git', 'rev-parse', 'HEAD'],
            capture_output=True,
            text=True,
            timeout=5
        )
        if result.returncode == 0:
            return result.stdout.strip()
        error(f"Failed to get current commit: {result.stderr.strip()}")
    except subprocess.TimeoutExpired:
        error("Timeout getting current commit")
    except FileNotFoundError:
        error("git not found")

def resolve_sha(short_sha: str) -> str:
    """Resolve a (possibly short) SHA to full 40-character SHA using git rev-parse."""
    if len(short_sha) == 40:
        return short_sha
    try:
        result = subprocess.run(
            ['git', 'rev-parse', short_sha],
            capture_output=True,
            text=True,
            timeout=5
        )
        if result.returncode == 0:
            full_sha = result.stdout.strip()
            if len(full_sha) == 40:
                return full_sha
        error(f"Cannot resolve SHA '{short_sha}': {result.stderr.strip() or 'not found in repository'}")
    except subprocess.TimeoutExpired:
        error(f"Timeout resolving SHA '{short_sha}'")
    except FileNotFoundError:
        error("git not found - required for SHA resolution")

# -----------------------------------------------------------------------------
# Main
# -----------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description='Download pre-built CI artifacts for a Lean commit.',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
This script downloads pre-built binaries from GitHub Actions CI runs,
which is much faster than building from source (~30s vs 2-5min).

Artifacts are cached in ~/.cache/lean_build_artifact/ for reuse.

Examples:
  build_artifact.py                   # Download for current HEAD
  build_artifact.py --sha abc1234     # Download for specific commit
  build_artifact.py --clear-cache     # Clear cache to free disk space
"""
    )

    parser.add_argument('--sha', metavar='SHA',
                        help='Commit SHA to download artifact for (default: current HEAD)')
    parser.add_argument('--clear-cache', action='store_true',
                        help='Clear artifact cache and exit')
    parser.add_argument('--quiet', '-q', action='store_true',
                        help='Suppress progress messages (still prints result path)')

    args = parser.parse_args()

    # Handle cache clearing
    if args.clear_cache:
        clear_cache()
        return

    # Get commit SHA
    if args.sha:
        sha = resolve_sha(args.sha)
    else:
        sha = get_current_commit()

    if not args.quiet:
        info(f"Commit: {sha[:12]}")

    if is_cached(sha):
        if not args.quiet:
            success("Using cached artifact")
        print(get_cache_path(sha))
        return

    # Download prerequisites are unnecessary for a verified local toolchain.
    if not check_gh_available():
        error("gh CLI not available or not authenticated. Run 'gh auth login' first.")

    if not check_zstd_support():
        error("tar does not support zstd compression. Install zstd or a newer tar.")

    artifact_name = get_artifact_name()
    if artifact_name is None:
        error(f"No CI artifacts available for this platform ({platform.system()} {platform.machine()})")

    if not args.quiet:
        info(f"Platform: {artifact_name}")

    # Download artifact
    result = download_ci_artifact(sha, quiet=args.quiet)

    if result is CI_FAILED:
        if not args.quiet:
            print()  # End the "downloading..." line
        error(f"CI build failed for commit {sha[:12]}")
    elif result is None:
        if not args.quiet:
            print()  # End the "downloading..." line
        error(f"No CI artifact available for commit {sha[:12]}")
    else:
        if not args.quiet:
            print(color("done", Colors.GREEN))
        print(result)

if __name__ == '__main__':
    main()
