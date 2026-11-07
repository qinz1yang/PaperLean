# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys

# Prepare real compiler PID aliases before the executable inherits this process.
if len(sys.argv) == 4 and sys.argv[1] == "--plant":
    mode, compiler = sys.argv[2:]
    pid = os.getpid()
    for suffix in [str(pid), *(f"{pid}-{generation}" for generation in range(3))]:
        path = f"Tiny.olean.tmp.{suffix}"
        if mode == "hard":
            os.link("sentinel", path)
        elif mode == "symlink":
            os.symlink("sentinel", path)
        else:
            os.mkfifo(path)
    os.execv(compiler, [compiler, "-o", "Tiny.olean", "Tiny.lean"])

root = Path(sys.argv[1]).resolve() / "regions"
root.mkdir()
compiler = shutil.which("lean")
source = b"theorem ex : True := True.intro\n"
reference = root / "reference"
reference.mkdir()
(reference / "Tiny.lean").write_bytes(source)
subprocess.run([compiler, "-o", "Tiny.olean", "Tiny.lean"], cwd=reference, check=True, timeout=60)
gold = (reference / "Tiny.olean").read_bytes()
assert gold.startswith(b"olean")

for mode, filetype in (("hard", stat.S_ISREG), ("symlink", stat.S_ISLNK), ("fifo", stat.S_ISFIFO)):
    d = root / mode
    d.mkdir()
    (d / "sentinel").write_text("untouched")
    (d / "Tiny.lean").write_bytes(source)
    child = subprocess.Popen([sys.executable, str(Path(__file__).resolve()), "--plant", mode, compiler], cwd=d)
    try:
        assert child.wait(timeout=60) == 0
    finally:
        if child.poll() is None:
            child.kill()
            child.wait()
    assert (d / "sentinel").read_bytes() == b"untouched", mode
    assert (d / "Tiny.olean").read_bytes() == gold, mode
    assert stat.S_IMODE((d / "Tiny.olean").stat().st_mode) == stat.S_IMODE((reference / "Tiny.olean").stat().st_mode)
    for suffix in [str(child.pid), *(f"{child.pid}-{generation}" for generation in range(3))]:
        assert filetype((d / f"Tiny.olean.tmp.{suffix}").lstat().st_mode)

driver = Path(__file__).with_suffix(".lean")
for version in ("v2", "v3"):
    subprocess.run([compiler, "--run", driver, root / version, version], check=True, timeout=60)
