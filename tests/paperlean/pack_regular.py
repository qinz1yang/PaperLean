# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
import os
from pathlib import Path
import shutil
import subprocess
import sys

work = Path(sys.argv[1]).resolve() / "regular-packs"
work.mkdir()
driver = Path(__file__).resolve().with_suffix(".lean")
lean = shutil.which("lean")


def run(args):
    return subprocess.run([lean, "--run", driver, *map(str, args)], cwd=work,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          timeout=30, check=True).stdout.strip()


def verify(path):
    assert run(["verify", path]) == ""


root = work / "lib"
root.mkdir()
source = work / "Source.lean"
source.write_text("def value : Nat := 17\n")
original = work / "Original.olean"
subprocess.run([lean, "-o", original, source], cwd=work, check=True, timeout=30)
(root / "Source.olean").symlink_to(original)
os.mkfifo(root / "Skipped.olean")
pack = work / "source.pack"
# The FIFO has an artifact extension, and the other input is a legitimate regular symlink.
assert run(["pack", root, pack]) == "1"
verify(pack)
(root / "Skipped.olean").unlink()

cache = work / "cache"
current = cache / run(["cache", cache, root])
verify(current)
identity = current.with_name("id-" + current.name)
before = current.stat()
assert cache / run(["cache", cache, root]) == current
assert current.stat().st_ino == before.st_ino, "warm regular pack was rebuilt"

current.unlink()
os.mkfifo(current)
assert cache / run(["cache", cache, root]) == current
assert current.is_file()
verify(current)

# A readable symlink to a complete pack remains usable without mutating its target.
target = work / "target.paperlean"
assert run(["pack", root, target]) == "1"
current.unlink()
current.symlink_to(target)
identity.unlink()
shutil.copyfile(target.with_name("id-" + target.name), identity)
assert cache / run(["cache", cache, root]) == current
assert current.is_symlink()
verify(current)

# Evict an old special file without opening it. A directory with a pack-like name is preserved.
old = current.parent / "old.paperlean"
os.mkfifo(old)
os.utime(old, (1, 1))
directory = current.parent / "directory.paperlean"
directory.mkdir()
(directory / "keep").write_text("untouched")
os.utime(directory, (1, 1))
for n in range(2):
    (current.parent / f"retained-{n}.paperlean").write_text("newer")
assert cache / run(["cache", cache, root]) == current
assert not old.exists()
assert (directory / "keep").read_text() == "untouched"

# A malformed regular pack is rebuilt. A current directory is left in place and declined.
current.unlink()
current.write_text("incomplete pack")
assert cache / run(["cache", cache, root]) == current
verify(current)
current.unlink()
current.mkdir()
(current / "keep").write_text("untouched")
assert run(["cache", cache, root]) == "none"
assert (current / "keep").read_text() == "untouched"
