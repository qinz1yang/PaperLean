#!/usr/bin/env python3
"""Build the test header-snapshot pair, reusing it only while its file identities still match.

This is a producer-before-consumer test cache, not an authentication boundary or an atomic update
protocol for already running snapshot readers. Test imports must remain stable after this fixture
finishes. A receipt is written last; missing/invalid receipts always require regeneration.
"""
from contextlib import ExitStack, contextmanager
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import tempfile


OPTIONS = ["-DprintMessageEndPos=true", "-Dlinter.all=false", "-DElab.inServer=true"]
PARTS = {"olean", "oleanServer", "oleanPrivate", "irSig", "ir"}
FORMAT = "lean-test-header-snapshots-identity-v2"


def identity(path):
    s = os.stat(path)
    if not stat.S_ISREG(s.st_mode):
        raise ValueError(f"not a regular file: {path}")
    return [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns]


def identities(paths):
    return {str(path): identity(path) for path in sorted(paths)}


def read_json(path):
    # O_NONBLOCK prevents a damaged receipt/deps FIFO from blocking the test fixture.
    fd = os.open(path, os.O_RDONLY | getattr(os, "O_NONBLOCK", 0))
    with os.fdopen(fd, "rb") as handle:
        s = os.fstat(handle.fileno())
        if not stat.S_ISREG(s.st_mode) or s.st_size > 16 * 1024 * 1024:
            raise ValueError(f"invalid metadata file: {path}")
        before = [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns]
        data = json.load(handle)
        s = os.fstat(handle.fileno())
        after = [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns]
        if before != after or after != identity(path):
            raise ValueError(f"metadata changed while read: {path}")
        return data


def dependencies(snapshots):
    paths = set()
    for snapshot in snapshots:
        rows = read_json(str(snapshot) + ".deps")
        if not isinstance(rows, list) or not rows:
            raise ValueError("snapshot dependency list is empty or invalid")
        for row in rows:
            if not isinstance(row, dict) or not row or not set(row) <= PARTS:
                raise ValueError("invalid snapshot dependency entry")
            for path in row.values():
                if not isinstance(path, str) or not path:
                    raise ValueError("invalid snapshot dependency path")
                # Keep '..' for the kernel's actual pathname resolution through symlinks. Paths
                # that cannot be classified unambiguously below are ineligible for warm reuse.
                paths.add(os.path.join(os.getcwd(), path))
    return paths


def search_roots(lean):
    raw = os.environ.get("LEAN_PATH")
    if raw is None:
        return []  # CTest's default: there is no explicit root preceding the built-in path.
    # SearchPath.parse retains empty entries. FilePath.join concatenates the separator even
    # when the left side is empty, so "" / "Pkg" names /Pkg (the drive root on Windows).
    explicit = [Path(os.path.abspath(os.sep) if part == "" else os.path.join(os.getcwd(), part))
                for part in raw.split(os.pathsep)]
    if len(explicit) > 64:
        return None
    try:
        query = subprocess.run([lean, "--print-libdir"], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                               text=True, check=False, timeout=30)
    except (OSError, subprocess.SubprocessError, UnicodeError):
        return None
    lines = query.stdout.splitlines()
    if query.returncode or len(lines) != 1 or not Path(lines[0]).is_absolute():
        return None
    return explicit + [Path(lines[0])]


def member(path, directory=False):
    try:
        mode = path.stat().st_mode
    except (FileNotFoundError, NotADirectoryError):
        return False
    return stat.S_ISDIR(mode) if directory else True


def namespace_witness(paths, roots):
    if roots is None or any(".." in root.parts for root in roots):
        return None  # Do not guess where an unclassifiable artifact was selected.
    if not roots:
        return "builtin-only"
    packages, interpretations = set(), set()
    suffixes = (".olean.private", ".olean.server", ".olean", ".ir.sig", ".ir")
    for path in paths:
        file = Path(path)
        if ".." in file.parts:
            return None
        matches = set()
        for root in roots:
            try:
                parts = file.relative_to(root).parts
            except ValueError:
                continue
            if not parts:
                return None
            suffix = next((s for s in suffixes if parts[-1].endswith(s)), None)
            if suffix is None:
                return None
            if len(parts) == 1:
                package = parts[0][:-len(suffix)]
            else:
                package = parts[0]
            if not package:
                return None
            matches.add((root, package))
            packages.add(package)
        if not matches:
            return None  # No lexical route from any known search root to this artifact.
        # Overlapping roots can give several possible module names for the same path. Keep ALL
        # their package selectors: a change to any plausible interpretation forces a miss.
        interpretations.add(frozenset(matches))
    if len(packages) * len(roots) > 4096:
        return None
    rows, selected = [], {}
    try:
        for package in sorted(packages):
            members = []
            for root in roots:
                # Exactly SearchPath.findWithExt: choose by the top-level package, even if the
                # eventual nested .olean does not exist. No directory walk or file-content reads.
                members.append((str(root), member(root / package, True), member(root / (package + ".olean"))))
            selected[package] = next((Path(root) for root, directory, olean in members if directory or olean), None)
            rows.append((package, members))
    except OSError:
        return None  # An unreadable selector cannot authorize reuse.
    if any(selected[package] != root for matches in interpretations for root, package in matches):
        return None  # A possible interpretation disagrees with selection: conservatively rebuild.
    return hashlib.sha256(json.dumps(rows, separators=(",", ":")).encode()).hexdigest()


@contextmanager
def locked(path):
    # Lock files remain in place: unlinking them would let another writer lock a different inode.
    with open(path, "a+b") as handle:
        if os.name == "nt":
            import msvcrt
            handle.seek(0)
            handle.write(b"\0")
            handle.flush()
            handle.seek(0)
            msvcrt.locking(handle.fileno(), msvcrt.LK_LOCK, 1)
            try:
                yield
            finally:
                handle.seek(0)
                msvcrt.locking(handle.fileno(), msvcrt.LK_UNLCK, 1)
        else:
            import fcntl
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
            yield


def remove(path):
    try:
        os.unlink(path)
    except FileNotFoundError:
        pass
    except IsADirectoryError:
        # Only an empty malformed cache directory is removable; never recursively delete it.
        os.rmdir(path)


def main():
    selected = shutil.which("lean")
    if selected is None:
        raise RuntimeError("lean is not on PATH")
    lean = os.path.abspath(selected)
    snapshots = [Path(os.path.abspath(os.environ[key])) for key in
                 ("LEAN_HEADER_SNAPSHOT_LEAN", "LEAN_HEADER_SNAPSHOT_INIT")]
    outputs = [str(path) + suffix for path in snapshots for suffix in ("", ".deps")]
    receipt = str(snapshots[0]) + ".receipt.json"
    lock_paths = [str(snapshot) + ".lock" for snapshot in snapshots]
    if len(set(outputs + [receipt] + lock_paths)) != 7:
        raise ValueError("snapshot, .deps, receipt and lock paths must be distinct")
    for snapshot in snapshots:
        snapshot.parent.mkdir(parents=True, exist_ok=True)

    def context():
        return {"format": FORMAT, "cwd": os.getcwd(), "lean": lean, "lean_id": identity(lean),
                "producer_id": identity(__file__), "options": OPTIONS,
                "environment_sha256": hashlib.sha256(json.dumps({k: v for k, v in os.environ.items()
                    if k.startswith(("LEAN_", "ELAN_", "PAPERLEAN_"))}, sort_keys=True).encode()).hexdigest()}

    with ExitStack() as locks:
        # Sorting per-output locks also serializes invocations with overlapping snapshot pairs.
        for path in sorted(lock_paths):
            locks.enter_context(locked(path))
        roots = search_roots(lean)
        try:
            recorded = read_json(receipt)
            paths = dependencies(snapshots)
            witness = namespace_witness(paths, roots)
            if (isinstance(recorded, dict) and set(recorded) == {"context", "outputs", "artifacts", "namespace"}
                    and witness is not None and recorded["namespace"] == witness
                    and recorded["context"] == context()
                    and recorded["outputs"] == identities(outputs)
                    and recorded["artifacts"] == identities(paths)):
                return
        except (OSError, ValueError, TypeError):
            pass

        # Existing metadata can supply the complete pre-generation dependency set even when its
        # receipt is missing. It does not authorize reuse of any existing snapshot bytes.
        try:
            known = dependencies(snapshots)
        except (OSError, ValueError, TypeError):
            known = set()
        remove(receipt)
        for path in outputs:
            remove(path)
        for _ in range(3):
            before_context = context()
            before_namespace = namespace_witness(known, roots)
            try:
                before = identities(known) if known else None
            except OSError:
                before = None
            with ExitStack() as temps:
                candidates = []
                for snapshot, text in zip(snapshots, ("import Lean\n", "")):
                    directory = temps.enter_context(tempfile.TemporaryDirectory(
                        prefix=".lean-header-", dir=snapshot.parent))
                    candidate = Path(directory) / "header.snap"
                    # Options must match the elab* runners' saved command state.
                    subprocess.run([lean, "--stdin", "--incr-header-save=" + str(candidate), *OPTIONS],
                                   input=text, text=True, check=True)
                    candidates.append(candidate)
                paths = dependencies(candidates)
                after = identities(paths)
                after_namespace = namespace_witness(paths, roots)
                if (before is None or before != after or before_context != context()
                        or before_namespace != after_namespace):
                    # On first initialization, discover the dependencies and generate again with
                    # a complete before/after identity check. Also retry a changed import graph.
                    known = paths
                    continue
                for source, destination in zip(candidates, snapshots):
                    os.replace(str(source) + ".deps", str(destination) + ".deps")
                    os.replace(source, destination)
                if (after != identities(paths) or before_context != context()
                        or after_namespace != namespace_witness(paths, roots)):
                    for path in outputs:
                        remove(path)
                    known = paths
                    continue
                recorded = {"context": before_context, "outputs": identities(outputs), "artifacts": after,
                            "namespace": after_namespace}
                # Publication completion marker for BOTH snapshots. A crash between output
                # renames leaves no receipt, so the next producer invocation cannot warm-hit.
                fd, temporary = tempfile.mkstemp(prefix=".lean-header-receipt-", dir=snapshots[0].parent)
                try:
                    with os.fdopen(fd, "w") as handle:
                        json.dump(recorded, handle, sort_keys=True)
                        handle.write("\n")
                        handle.flush()
                        os.fsync(handle.fileno())
                    os.replace(temporary, receipt)
                finally:
                    remove(temporary)
                return
        raise RuntimeError("header snapshot dependencies changed during generation; no receipt published")


if __name__ == "__main__":
    main()
