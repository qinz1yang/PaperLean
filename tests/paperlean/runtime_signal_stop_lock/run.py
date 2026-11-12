#!/usr/bin/env python3
"""Build and run the Signal.stop/event-loop-lock regression.

On Linux a preload library forces the two-stop interleaving: both calls observe
the running signal before either takes the event-loop lock, so 0.2.3 drops the
loop's reference twice.  The harness checks the resulting reference count and
then runs the callback-race stress loop.  The preload barrier is Linux-only,
so other platforms skip this test rather than run a chance-dependent loop.
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
    p.add_argument("--cc", default="cc")
    p.add_argument("--out", required=True, type=Path)
    a = p.parse_args()
    if not sys.platform.startswith("linux"):
        print("SKIP: the deterministic Signal.stop barrier targets Linux")
        return 0
    src = Path(__file__).resolve().parent
    out = a.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    exe = out / "signal_stop_race"
    env = os.environ.copy()
    argv = [str(exe)]
    link_extra = []
    import shlex
    import shutil
    cc = shlex.split(a.cc)
    if not cc:
        for candidate in ("clang", "cc", "gcc"):
            found = shutil.which(candidate)
            if found:
                cc = [found]
                break
    if not cc:
        raise SystemExit("no C compiler found for the signal preload")
    lib = out / "libstopbarrier.so"
    subprocess.run([*cc, "-shared", "-fPIC", "-nostdlib", "-O2",
                    str(src / "signal_stop_barrier.c"), "-o", str(lib)], check=True)
    link_extra = [str(lib)]
    preload = env.get("LD_PRELOAD")
    env["LD_PRELOAD"] = str(lib) + (":" + preload if preload else "")
    subprocess.run([str(a.leanc.resolve()), "-O1", "-g",
                    str(src / "signal_stop_race.c"), "-o", str(exe), *link_extra], check=True)
    cp = subprocess.run(argv, cwd=out, stdin=subprocess.DEVNULL, env=env,
                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                        text=True, timeout=50, preexec_fn=no_core)
    output = cp.stdout or ""
    (out / "run.txt").write_text(output)
    print(f"rc={cp.returncode}")
    print(output, end="")
    good = (cp.returncode == 0 and "stress completed" in output
            and "deterministic double stop: refs=2" in output
            and "signal barrier released" in output)
    return 0 if good else 1


if __name__ == "__main__":
    sys.exit(main())
