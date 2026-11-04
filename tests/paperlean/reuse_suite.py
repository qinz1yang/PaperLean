#!/usr/bin/env python3
# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Runs Lean's own test files with reuse and its oracle on (`PAPERLEAN_REUSE`, `PAPERLEAN_REUSE_ORACLE`)
and with nothing reused (`PAPERLEAN_EXACT`), with proofs in tasks and on the elaboration thread
(`-DElab.async=false`, where far more is reused), and compares exit code, messages, `.olean` (with its
parts), `.ilean` and `.c`. The messages leave out only the times that are printed and PaperLean's notice
that a further frontend turns reuse off (`normalize`).

A finding of the oracle in any run, and a run with reuse that a signal ends where none ended a run without,
fail the suite: no other run takes them back. Where the runs differ otherwise, both are repeated, and all
of them count. What varies with nothing reused says nothing about reuse (random numbers, tasks that
race, a `try?` whose fresh names reach the `.olean`), and what a run with reuse also gives the same as one
without is transient (a limit of wall-clock time, as of the SAT solver of `bv_decide`, under load).

reuse_suite.py [-j JOBS] [--out FILE] [--files F,...] [PILE ...]

Each file runs in its pile, as `run_test.sh` does: with the pile's options, its `.init.sh` and
`.before.sh`. Prints each finding, signal, difference and transient difference, and a summary, and exits
with 1 if there is a finding, a signal or a difference.
"""
import argparse
import hashlib
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

TESTS = Path(__file__).resolve().parent.parent
PILE_ARGS = "--root=.. -DprintMessageEndPos=true -Dlinter.all=false -DElab.inServer=true"
PILES = {
    "elab": PILE_ARGS + " -Dcompiler.postponeCompile=false",
    "elab_fail": PILE_ARGS,
    "elab_bench": PILE_ARGS + " -Dcompiler.postponeCompile=false",
    "compile": "-Dcompiler.postponeCompile=false",
    "compile_bench": "-Dcompiler.postponeCompile=false",
    "../doc/examples": "-Dlinter.all=false",
}
# (the files that `tests/CMakeLists.txt` leaves out as flaky)
SKIP = {"async_select_channel.lean", "sync_mutex.lean"}
VARIANTS = {
    "exact": {"PAPERLEAN_EXACT": "1"},
    # (every search kept, as the problems of these files are small)
    "oracle": {"PAPERLEAN_REUSE": "1", "PAPERLEAN_REUSE_ORACLE": "1", "PAPERLEAN_REUSE_MIN_HEARTBEATS": "0"},
}
ARTIFACTS = ["olean", "olean.server", "olean.private", "ilean", "c"]
TIMEOUT = 600
REPEATS = 3
# What `lean` prints for a finding of the oracle (`lean_paperlean_speculation_fail`), then it exits.
ORACLE_FINDING = b"PaperLean: the reuse oracle found a difference:"
# PaperLean's notice that a frontend that a test starts turns reuse off (`Lean.PaperLean.Speculation`).
FURTHER_FRONTEND = re.compile(rb"^PaperLean: a further frontend in this process \(.*\): reuse of results and its "
                              rb"oracle are off from here on\n", re.M)
# A time as Lean prints it (`display_profiling_time`), with no space, of 3 digits, so also `1e+03ms`.
TIME = rb"\d+(?:\.\d+)?(?:e[-+]?\d+)?(?:ms|s)"
# The lines of the profiler (`time_task.cpp`), which it prints only above a threshold of time ...
PROFILER = re.compile(rb"^.* took " + TIME + rb"(?:\n|\Z)", re.M)
# ... the times at the end of a run, under their heading ...
CUMULATIVE = re.compile(rb"^cumulative profiling times:\n(?:\t[^\n]* " + TIME + rb"\n)*", re.M)
# ... what `normalize_measurements` of `util.sh` leaves out ...
MEASUREMENT = re.compile(rb"^measurement: (\S+) \S+(?: \S+)?$", re.M)
# ... the lines of `#time` (`Lean.Elab.Time`) and of `timeit "time"` ...
TIMED = re.compile(rb"^(time:? )" + TIME + rb"$", re.M)
# ... and what the `cbv` benchmarks print of a `Float`, `s!"{ms} ms"`, which has six decimals.
BENCH_MS = rb"\d+\.\d{6} ms"
BENCH = re.compile(rb"^(?:(?:cbv|decide): )?\w+(?: \d+)?: (?:cbv )?" + BENCH_MS + rb"(?:, kernel:? " + BENCH_MS
                   + rb")?(?: \(rfl\))?$", re.M)


def digest(path):
    try:
        return hashlib.sha1(path.read_bytes()).hexdigest()[:12]
    except OSError:
        return None


def normalize(output):
    """`output` without the times that Lean and the benchmarks print and PaperLean's notice of a further
    frontend, and nothing else: the profiler's lines go, as they come and go, and the others keep their names.
    Each format is matched as a whole line: a number before `s` may be mathematics (`hasLength 0 s = true`)."""
    output = FURTHER_FRONTEND.sub(b"", output)
    output = PROFILER.sub(b"", output)
    output = CUMULATIVE.sub(b"cumulative profiling times:\n", output)
    output = MEASUREMENT.sub(rb"measurement: \1 ...", output)
    output = TIMED.sub(rb"\1...", output)
    return BENCH.sub(lambda m: re.sub(BENCH_MS, b"... ms", m.group(0)), output)


def run(pile, file, variant, extra, out):
    """The results of `file` of `pile` under `variant`: exit code, digest of the output, of the artifacts;
    the output as compared, and as printed."""
    base = out / f"{variant}.{file}"
    env = {k: v for k, v in os.environ.items() if not k.startswith("PAPERLEAN_")}
    env.update(VARIANTS[variant], LEAN_BACKTRACE="0")
    if variant == "oracle":
        env["PAPERLEAN_REUSE_STATS"] = str(out / "stats")
    script = f"""
TEST_LEAN_ARGS=()
[ ! -f {shlex.quote(file)}.init.sh ] || source {shlex.quote(file)}.init.sh
[ ! -f {shlex.quote(file)}.before.sh ] || bash -- {shlex.quote(file)}.before.sh
exec lean {PILES[pile]} {extra} -o {base}.olean -i {base}.ilean -c {base}.c "${{TEST_LEAN_ARGS[@]}}" {shlex.quote(file)}
"""
    try:
        p = subprocess.run(["bash", "-c", script], cwd=TESTS / pile, env=env, stdin=subprocess.DEVNULL,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=TIMEOUT)
        rc, raw = p.returncode, p.stdout
        output = normalize(raw.replace(str(base).encode(), b"<ARTIFACT>"))
    except subprocess.TimeoutExpired as e:
        rc, raw, output = "timeout", e.stdout or b"", b""
    if (TESTS / pile / f"{file}.after.sh").exists():
        subprocess.run(["bash", "--", f"{file}.after.sh"], cwd=TESTS / pile, env=env, stdout=subprocess.DEVNULL,
                       stderr=subprocess.DEVNULL)
    r = {"exit": rc, "output": hashlib.sha1(output).hexdigest()[:12]}
    for a in ARTIFACTS:
        p = Path(f"{base}.{a}")
        r[a] = digest(p)
        p.unlink(missing_ok=True)
    for p in [Path(f"{base}.ir"), Path(f"{base}.ir.sig")]:
        p.unlink(missing_ok=True)
    return r, output, raw


def compare(pile, file, extra, out):
    """What differs for `file` of `pile`, whether repeated runs agree on it, and the findings of the oracle
    and the signals of all of them."""
    (out / "stats").unlink(missing_ok=True)
    res = {"pile": pile, "file": file, "extra": extra, "oracle": [], "signals": [], "differs": [],
           "unstable": [], "transient": [], "reuses": 0}
    exits = {"exact": [], "oracle": []}

    def invoke(variant):
        r, output, raw = run(pile, file, variant, extra, out)
        res["oracle"] += [l.decode("utf-8", "replace") for l in raw.splitlines() if ORACLE_FINDING in l]
        exits[variant].append(r["exit"])
        return r, output

    exact, exact_out = invoke("exact")
    oracle, oracle_out = invoke("oracle")
    kinds = [k for k in exact if exact[k] != oracle[k]]
    if (out / "stats").exists():
        for line in (out / "stats").read_text().splitlines():
            f = line.split("\t")
            res["reuses"] += int(f[1]) + int(f[5])
    if kinds:
        exacts, oracles = [exact], [oracle]
        for _ in range(REPEATS):
            exacts.append(invoke("exact")[0])
            oracles.append(invoke("oracle")[0])
        # (also what only a repeat shows)
        for k in [k for k in exact if len({r[k] for r in exacts + oracles}) > 1]:
            with_exact = {r[k] for r in exacts}
            with_reuse = {r[k] for r in oracles}
            if len(with_exact) > 1:
                res["unstable"].append(k)
            elif with_exact & with_reuse:
                res["transient"].append(k)
            else:
                res["differs"].append(k)
        res["exits"] = exits["oracle"]
        if res["differs"]:
            res["oracle_output"] = oracle_out.decode("utf-8", "replace")[-600:]
            res["exact_output"] = exact_out.decode("utf-8", "replace")[-600:]
    res["signals"] = sorted({x for x in exits["oracle"] if x != "timeout" and x < 0} - set(exits["exact"]))
    return res


def compare_all(pile, file, root):
    """`compare` in both modes, one after the other: a test file may write to fixed paths."""
    out = root / f"{pile.replace('/', '_')}.{file}"
    out.mkdir(parents=True, exist_ok=True)
    rs = [compare(pile, file, extra, out) for extra in ["", "-DElab.async=false"]]
    shutil.rmtree(out, ignore_errors=True)
    return rs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-j", "--jobs", type=int, default=os.cpu_count())
    ap.add_argument("--out", help="write one JSON line per run to this file")
    ap.add_argument("--files", help="only these files, comma-separated")
    ap.add_argument("piles", nargs="*", default=list(PILES))
    args = ap.parse_args()
    only = set(args.files.split(",")) if args.files else None
    todo = []
    for pile in args.piles:
        for f in sorted(p.name for p in (TESTS / pile).glob("*.lean")):
            if f in SKIP or (TESTS / pile / f"{f}.no_test").exists() or (only and f not in only):
                continue
            todo.append((pile, f))
    root = Path(tempfile.mkdtemp(prefix="reuse-suite."))
    log = open(args.out, "a") if args.out else None
    runs = reused = bad = unstable = transient = findings = signals = 0
    with ThreadPoolExecutor(args.jobs) as ex:
        for r in (r for rs in ex.map(lambda t: compare_all(*t, root), todo) for r in rs):
            runs += 1
            reused += r["reuses"] > 0
            unstable += bool(r["unstable"])
            transient += bool(r["transient"])
            if log:
                print(json.dumps(r), file=log, flush=True)
            if r["oracle"]:
                findings += 1
                print(f"ORACLE {r['pile']}/{r['file']} {r['extra']}:", flush=True)
                print("\n".join(r["oracle"]), flush=True)
            if r["signals"]:
                signals += 1
                ended = ", ".join(str(-x) for x in r["signals"])
                print(f"SIGNAL {r['pile']}/{r['file']} {r['extra']}: a run with reuse ended by signal {ended}, "
                      f"exit codes with reuse: {r['exits']}", flush=True)
            if r["transient"]:
                print(f"TRANSIENT {r['pile']}/{r['file']} {r['extra']}: {' '.join(r['transient'])}", flush=True)
            if r["differs"]:
                bad += 1
                print(f"DIFFERS {r['pile']}/{r['file']} {r['extra']}: {' '.join(r['differs'])}", flush=True)
                print(f"exit codes with reuse: {r['exits']}", flush=True)
                print(r["oracle_output"], flush=True)
    shutil.rmtree(root, ignore_errors=True)
    print(f"{runs} runs, {reused} with a reuse, {unstable} that vary without reuse, {transient} with a "
          f"transient difference, {findings} with a finding of the oracle, {signals} ended by a signal, "
          f"{bad} that differ")
    return 1 if findings or signals or bad or not reused else 0


if __name__ == "__main__":
    sys.exit(main())
