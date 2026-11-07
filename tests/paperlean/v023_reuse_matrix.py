#!/usr/bin/env python3
"""Run a bounded CLI batch/inServer × reuse/exact × explicit -j1/-j4 matrix.

This is NOT an LSP edit/server lifecycle test. PAPERLEAN_REUSE_MIN_HEARTBEATS=0
is a testing-only override ensuring small fixtures can hit; these timings must
not be reported as production performance. Requires an already-built PaperLean.
Usage: python3 reuse_matrix.py /absolute/path/to/lean [/path/to/v023_reuse_matrix.lean]
"""
import os
from pathlib import Path
import subprocess
import sys
import tempfile

lean = Path(sys.argv[1]).resolve(strict=True)
source = Path(sys.argv[2]).resolve(strict=True) if len(sys.argv) > 2 else Path(__file__).with_name("v023_reuse_matrix.lean")
baseline = None
with tempfile.TemporaryDirectory(prefix="lean-reuse-matrix-") as tmp:
    for in_server in [False, True]:
        for threads in [1, 4]:
            for mode in ["exact", "reuse"]:
                stats = Path(tmp) / f"{in_server}-{threads}-{mode}.stats"
                env = dict(os.environ)
                for key in list(env):
                    if key.startswith("PAPERLEAN_REUSE") or key in {"PAPERLEAN_EXACT", "LEAN_NUM_THREADS"}:
                        env.pop(key)
                env.update(PAPERLEAN_REUSE="1", PAPERLEAN_REUSE_MIN_HEARTBEATS="0",
                           PAPERLEAN_REUSE_STATS=str(stats))
                if mode == "exact":
                    env["PAPERLEAN_EXACT"] = "1"
                else:
                    env["PAPERLEAN_REUSE_ORACLE"] = "1"
                args = [str(lean), f"-j{threads}", f"-DElab.inServer={str(in_server).lower()}",
                        "-Dinternal.cmdlineSnapshots=true", str(source)]
                result = subprocess.run(args, env=env, capture_output=True, text=True, timeout=180)
                if result.returncode != 0:
                    raise AssertionError((args, mode, result.returncode, result.stdout, result.stderr))
                diagnostics = (result.stdout, result.stderr)
                if baseline is None:
                    baseline = diagnostics
                elif diagnostics != baseline:
                    raise AssertionError((args, mode, "semantic output differs", diagnostics, baseline))
                records = [line.split("\t") for line in stats.read_text().splitlines() if line]
                if len(records) != 1 or len(records[0]) != 9:
                    raise AssertionError((args, "missing/unexpected reuse statistics", records))
                hits, searched, rejected = map(int, records[0][1:4])
                section_hits = int(records[0][5])
                if mode == "reuse" and hits == 0:
                    raise AssertionError((args, "zero typeclass reuse hits; matrix did not exercise reuse", records))
                if mode == "exact" and (hits != 0 or section_hits != 0):
                    raise AssertionError((args, "exact mode unexpectedly reused", records))
                print(f"PASS inServer={in_server} -j{threads} {mode} "
                      f"tc_hits={hits} searched={searched} rejected={rejected} section_hits={section_hits}")
