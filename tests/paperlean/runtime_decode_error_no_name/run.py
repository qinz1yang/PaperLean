#!/usr/bin/env python3
"""Build and run the no-file-name I/O error decoding regression.

Both runs link against the selected toolchain's runtime.  `flock` exercises the
public Handle.lock operation while another process holds the file lock and
SIGUSR1 interrupts the blocking flock(2).  `decode` calls the decoder directly
for EINTR and ENOENT with a null file name.  On 0.2.3 either path dereferences
the null name and crashes.
"""
import argparse
import os
from pathlib import Path
import resource
import subprocess
import sys


def no_core() -> None:
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--leanc", required=True, type=Path)
    p.add_argument("--out", required=True, type=Path)
    a = p.parse_args()
    if not (sys.platform.startswith("linux") or sys.platform == "darwin"):
        print("SKIP: POSIX only")
        return 0
    src = Path(__file__).resolve().parent
    out = a.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    exe = out / "eintr_probe"
    subprocess.run([str(a.leanc.resolve()), "-O1", "-g",
                    str(src / "eintr_probe.c"), "-o", str(exe)], check=True)
    ok = True
    for mode, expected in (("flock", "interrupted lock ok"),
                           ("decode", "decode ENOENT ok")):
        cp = subprocess.run([str(exe), mode], cwd=out, stdin=subprocess.DEVNULL,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            text=True, timeout=30, preexec_fn=no_core)
        output = cp.stdout or ""
        (out / f"{mode}.txt").write_text(output)
        good = cp.returncode == 0 and expected in output
        print(f"{mode}: rc={cp.returncode} ok={good}")
        print(output, end="")
        ok = ok and good
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
