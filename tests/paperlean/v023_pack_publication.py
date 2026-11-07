# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
import fcntl
import os
from pathlib import Path
import stat
import subprocess
import sys
import time

root = Path(sys.argv[1])
driver = sys.argv[2]
sentinel = b"keep original bytes\n"
(root / "occupied").mkdir()
(root / "occupied" / "sentinel").write_bytes(sentinel)
victim = root / "unrelated"
victim.write_bytes(sentinel)
with subprocess.Popen(["lean", "-j4", "--run", driver, str(root)],
                      stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True) as child:
    def wait_for(predicate):
        for _ in range(1500):
            if predicate():
                return
            if child.poll() is not None:
                raise AssertionError(child.stdout.read())
            time.sleep(.01)
        raise AssertionError("timed out waiting for writer")
    fd = os.open(root, os.O_RDONLY | os.O_DIRECTORY)
    try:
        protected = {}
        for kind, name in enumerate(["hashes", "empty", "out.paperlean", "id-out.paperlean", "binding"]):
            for n in range(-1,8):
                suffix = f".tmp.{child.pid}" + (f"-{n}" if n >= 0 else "")
                p = root / (name + suffix)
                k = (kind + n + 1) % 3
                if k == 0: os.link(victim, p)
                elif k == 1: p.symlink_to(victim)
                else: os.mkfifo(p)
                protected[p] = (p.lstat().st_ino, p.lstat().st_mode)
        (root / "start").touch()
        wait_for(lambda: (root / "ready").exists())
        old = (root / "out.paperlean").stat()
        # Wait with an official reader's prior pack inode open and shared-locked.
        with (root / "out.paperlean").open("rb") as previous:
            fcntl.flock(previous, fcntl.LOCK_SH)
            fcntl.flock(fd, fcntl.LOCK_EX)
            (root / "writers").touch()
            def complete_temps():
                pending = [p for p in root.glob(f"out.paperlean.tmp.{child.pid}-*")
                           if p not in protected and stat.S_IMODE(p.stat().st_mode) == 0o444]
                return len(pending) == 2
            wait_for(complete_temps)
            assert (root / "out.paperlean").stat().st_ino == old.st_ino
            fcntl.flock(fd, fcntl.LOCK_UN)
            output, _ = child.communicate(timeout=15)
            assert child.returncode == 0 and "publications passed" in output, output
            assert os.fstat(previous.fileno()).st_ino == old.st_ino
        assert (root / "out.paperlean").stat().st_ino != old.st_ino
        for p, identity in protected.items():
            st = p.lstat()
            assert (st.st_ino, st.st_mode) == identity, p
        assert victim.read_bytes() == sentinel
        assert (root / "occupied" / "sentinel").read_bytes() == sentinel
        assert not list(root.glob(f"occupied.tmp.{child.pid}-*"))
        for p in ["out.paperlean", "id-out.paperlean", "binding"]:
            assert stat.S_IMODE((root / p).stat().st_mode) == 0o444
        print(output, end="")
    finally:
        os.close(fd)
        if child.poll() is None:
            child.kill()
            child.wait()
