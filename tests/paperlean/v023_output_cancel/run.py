"""Compile the POSIX oracle and run one session-isolated Lean process per case."""
import argparse
import json
import os
from pathlib import Path
import signal
import subprocess
import sys


def run_case(argv, env, seconds):
    p = subprocess.Popen(argv, start_new_session=True, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, text=True, env=env)
    timed_out = False
    try:
        out, err = p.communicate(timeout=seconds)
    except subprocess.TimeoutExpired:
        timed_out = True
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        out, err = p.communicate()
    finally:
        # Also clean up an actual stray child if the Lean main process exited early.
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    return {"argv": argv, "returncode": p.returncode, "timeout": timed_out,
            "stdout": out, "stderr": err}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--threads", nargs="+", type=int, default=[1, 4])
    parser.add_argument("--timeout", type=float, default=15)
    parser.add_argument("--cc", default="cc")
    args = parser.parse_args()
    src = Path(__file__).resolve().parent
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    mac = sys.platform == "darwin"
    lib = out / ("libu08oracle.dylib" if mac else "libu08oracle.so")
    cc = [args.cc, "-std=c11", "-O2", "-fPIC", "-dynamiclib" if mac else "-shared",
          str(src / "oracle.c"), "-o", str(lib)]
    if not mac:
        cc.append("-ldl")
    subprocess.run(cc, check=True)
    # The Lean source calls three C probes directly. Build a native executable so
    # those extern names are linked rather than resolving interpreter wrapper names.
    lean = args.lean.resolve()
    driver = out / "cancel-output"
    subprocess.run([lean, "--root=" + str(src), "-c", out / "Main.c",
                    src / "OutputCancel.lean"], check=True)
    subprocess.run([lean.parent / "leanc", "-O2", "-o", driver, out / "Main.c", lib], check=True)
    env = os.environ.copy()
    var = "DYLD_INSERT_LIBRARIES" if mac else "LD_PRELOAD"
    env[var] = str(lib) + (":" + env[var] if env.get(var) else "")
    results = []
    for jobs in args.threads:
        for mode in ["blocked", "closed"]:
            fifo = out / f"ready-{jobs}-{mode}"
            os.mkfifo(fifo, 0o600)
            env["LEAN_NUM_THREADS"] = str(jobs)
            argv = [str(driver), sys.executable,
                    str(src / "child.py"), mode, str(fifo)]
            result = run_case(argv, env, args.timeout)
            result["ok"] = result["returncode"] == 0 and not result["timeout"] and (
                f"{mode}: interrupted and reaped" in result["stdout"].splitlines())
            result["workers"] = jobs
            results.append(result)
            (out / "results.json").write_text(json.dumps(results, indent=2) + "\n")
            print(f"{mode} -j{jobs} rc={result['returncode']} timeout={result['timeout']}",
                  flush=True)
    return int(not all(r["ok"] for r in results))


if __name__ == "__main__":
    sys.exit(main())
