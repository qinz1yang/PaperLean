#!/usr/bin/env python3
"""Exercise realPath(3) failures that are not ENOENT.

A regular file in the path yields ENOTDIR (20) and an unreadable directory
yields EACCES (13).  On 0.2.3 every failure is hardcoded to noFileOrDirectory
with errno 2.  The permission case is skipped when running as root, where
chmod 000 is not enforced.
"""
import argparse
import os
from pathlib import Path
import subprocess
import sys


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--lean", required=True, type=Path)
    p.add_argument("--out", required=True, type=Path)
    a = p.parse_args()
    src = Path(__file__).resolve().parent
    out = a.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    plain = out / "plain"
    plain.write_text("not a directory\n")
    secret = out / "secret"
    secret.mkdir()
    child = secret / "child"
    permission = "" if os.geteuid() == 0 else str(child)
    secret.chmod(0)
    try:
        cp = subprocess.run(
            [str(a.lean.resolve()), "--run", str(src / "RealPathErrno.lean"),
             str(plain / "child"), permission],
            cwd=out, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, text=True, timeout=30)
    finally:
        secret.chmod(0o700)
    output = cp.stdout
    print(f"rc={cp.returncode}")
    print(output, end="")
    return 0 if cp.returncode == 0 and "preserved error code 20" in output else 1


if __name__ == "__main__":
    sys.exit(main())
