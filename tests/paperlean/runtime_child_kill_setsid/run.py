#!/usr/bin/env python3
"""Run the setsid Child.kill regression on one or more Lean worker counts.

The preload library interposes setsid() in the forked child, writes a marker just
before the real setsid(), and delays it.  The Lean driver calls Child.kill as soon
as the marker appears.  On 0.2.3 killpg(pid) has no group yet and fails with ESRCH,
so the driver reports an error and wait observes the delayed child's normal exit.
With the fix Child.kill falls back to kill(pid) and wait reports 137.
"""
import argparse
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--lean", required=True, type=Path)
    p.add_argument("--cc", default="")
    p.add_argument("--out", required=True, type=Path)
    a = p.parse_args()
    if not sys.platform.startswith("linux"):
        print("SKIP: this regression targets Linux")
        return 0
    src = Path(__file__).resolve().parent
    out = a.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    cc = shlex.split(a.cc)
    if not cc:
        for candidate in ("clang", "cc", "gcc"):
            found = shutil.which(candidate)
            if found:
                cc = [found]
                break
    if not cc:
        raise SystemExit("no C compiler found (tried clang, cc, gcc)")
    lib = out / "libsetsiddelay.so"
    subprocess.run([*cc, "-shared", "-fPIC", "-nostdlib", "-O2",
                    str(src / "setsid_delay.c"), "-o", str(lib)], check=True)
    ok = True
    for workers in (1, 4):
        marker = out / f"marker-{workers}"
        try:
            marker.unlink()
        except FileNotFoundError:
            pass
        env = {k: v for k, v in os.environ.items()
               if not k.startswith(("PAPERLEAN_", "ELAN_", "LEAN_"))}
        home = out / "home"
        (home / ".cache").mkdir(parents=True, exist_ok=True)
        env.update(HOME=str(home), XDG_CACHE_HOME=str(home / ".cache"),
                   PL_SETSID_MARKER=str(marker), LEAN_NUM_THREADS=str(workers))
        preload = env.get("LD_PRELOAD")
        env["LD_PRELOAD"] = str(lib) + (":" + preload if preload else "")
        cp = subprocess.run(
            [str(a.lean.resolve()), "--run", str(src / "SetsidKill.lean"), str(marker)],
            env=env, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, text=True, timeout=40)
        output = cp.stdout
        (out / f"run-{workers}.txt").write_text(output)
        good = cp.returncode == 0 and "kill=ok: () code=137" in output
        print(f"workers={workers} rc={cp.returncode} ok={good}")
        print(output, end="")
        ok = ok and good
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
