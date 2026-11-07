#!/usr/bin/env python3
"""Opt-in depth-30 RC overflow regression; never part of the daily test suite.

Usage: python3 tests/stress/rc_overflow.py /absolute/path/to/lean
The child has a 300-second CPU limit, 360-second wall limit, a 20-GiB address
space ceiling, and core dumps disabled. The depth-30 case needs about 12 GiB
of physical memory. Address-space limits have platform-dependent enforcement;
run on a suitably provisioned host. A timeout/resource error is a FAILED test,
not evidence that the kernel rejected the invalid declaration correctly.
"""
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import tempfile


def child_limits():
    resource.setrlimit(resource.RLIMIT_CPU, (300, 300))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    ceiling = 20 * 1024**3
    _, hard = resource.getrlimit(resource.RLIMIT_AS)
    if hard != resource.RLIM_INFINITY:
        ceiling = min(ceiling, hard)
    resource.setrlimit(resource.RLIMIT_AS, (ceiling, ceiling))


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: rc_overflow.py /absolute/path/to/lean")
    lean = Path(sys.argv[1]).resolve(strict=True)
    tests = Path(__file__).resolve().parents[1]
    source = (tests / "elab" / "14838.lean").read_text()
    daily_depth = "private def depth := 12"
    if source.count(daily_depth) != 1:
        raise SystemExit("daily RC regression changed: review the stress transformation")
    source = source.replace(daily_depth, "private def depth := 30")
    with tempfile.TemporaryDirectory(prefix="lean-rc-overflow-") as tmp:
        case = Path(tmp) / "rc_overflow.lean"
        case.write_text(source)
        child = subprocess.Popen([str(lean), str(case)], start_new_session=True,
                                 preexec_fn=child_limits)
        try:
            return child.wait(timeout=360)
        except subprocess.TimeoutExpired:
            os.killpg(child.pid, signal.SIGKILL)
            child.wait()
            print("RC overflow stress exceeded its wall-time limit", file=sys.stderr)
            return 1
        except BaseException:
            if child.poll() is None:
                os.killpg(child.pid, signal.SIGKILL)
                child.wait()
            raise


if __name__ == "__main__":
    status = main()
    # Preserve failure even for a child terminated by a signal.
    raise SystemExit(0 if status == 0 else 1)
