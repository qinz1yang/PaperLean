#!/usr/bin/env python3
"""S37: exercise the actual header builder and loader with fixed executable mtime.

The shadow module named Lean keeps this fixture small and leaves installed toolchain artifacts
untouched. It is still the exact `import Lean` consumed by build_lean_header_snapshots.sh. The test
accepts a rebuilt snapshot or transparent loader fallback, but never a stale result or crash.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source-root", type=Path, required=True)
    p.add_argument("--lean", type=Path, required=True)
    p.add_argument("--work", type=Path, required=True)
    a = p.parse_args()
    root, lean, work = (x.resolve() for x in (a.source_root, a.lean, a.work))
    work.mkdir(parents=True, exist_ok=True)
    if any(work.iterdir()):
        raise SystemExit("--work must be empty")
    lib = work / "lib"
    lib.mkdir()
    env = {k: v for k, v in os.environ.items() if not k.startswith("PAPERLEAN_")}
    for key in ("LEAN_OLEAN_PACK", "LEAN_IMPORT_IMAGE", "ELAN_TOOLCHAIN", "LEAN_SYSROOT"):
        env.pop(key, None)
    env.update(PATH=str(lean.parent) + os.pathsep + env.get("PATH", ""), LEAN_PATH=str(lib),
               LEAN_HEADER_SNAPSHOT_LEAN=str(work / "lean.snap"),
               LEAN_HEADER_SNAPSHOT_INIT=str(work / "init.snap"))
    flags = ["-DprintMessageEndPos=true", "-Dlinter.all=false", "-DElab.inServer=true"]
    commands = []

    def run(args, label):
        commands.append(args)
        label = f"{len(commands):02d}-" + label
        r = subprocess.run(args, cwd=work, env=env, capture_output=True, timeout=120)
        (work / (label + ".stdout")).write_bytes(r.stdout)
        (work / (label + ".stderr")).write_bytes(r.stderr)
        (work / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
        if r.returncode:
            raise SystemExit(f"{label} failed ({r.returncode}); snapshot invalidation/fallback gate failed: {work}")
        return r.stdout

    def identity(path):
        s = path.stat()
        return [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns]

    def compile_module(name):
        run([str(lean), "-o", str(lib / (name + ".olean")), str(work / (name + ".lean"))], "compile-" + name)

    helper = ["bash", str(root / "tests/build_lean_header_snapshots.sh")]
    binary_before = identity(lean)
    (work / "V023SnapshotDep.lean").write_text("def v023SnapshotValue : Nat := 11\n")
    (work / "Lean.lean").write_text("import V023SnapshotDep\n")
    compile_module("V023SnapshotDep")
    compile_module("Lean")
    run(helper, "build-snapshots-before")
    snap = work / "lean.snap"
    snap_before = identity(snap)
    if snap.stat().st_mtime_ns < lean.stat().st_mtime_ns:
        raise SystemExit("precondition failed: the lean binary is newer than the freshly built snapshot")
    deps = json.loads((work / "lean.snap.deps").read_text())
    if str(lib / "V023SnapshotDep.olean") not in json.dumps(deps):
        raise SystemExit("fixture did not capture the shadow import artifact")
    (work / "Use.lean").write_text("import Lean\n#eval v023SnapshotValue\n")
    initial = run([str(lean), *flags, "--incr-load=" + str(snap), "Use.lean"], "initial-cached")
    if initial.strip() != b"11":
        raise SystemExit("initial snapshot did not produce the expected value")
    artifact = lib / "V023SnapshotDep.olean"
    artifact_before = hashlib.sha256(artifact.read_bytes()).hexdigest()
    # A new declaration ensures stale environment maps cannot pass merely because same-shaped
    # region replacement happens to redirect an old pointer to the new numeral's bytes.
    (work / "V023SnapshotDep.lean").write_text(
        "def v023SnapshotValue : Nat := 29\ndef v023SnapshotFresh : Nat := 29\n")
    compile_module("V023SnapshotDep")
    artifact_after = hashlib.sha256(artifact.read_bytes()).hexdigest()
    if artifact_before == artifact_after:
        raise SystemExit("import artifact did not change")
    (work / "Use.lean").write_text(
        "import Lean\n#eval v023SnapshotValue\nexample : v023SnapshotFresh = 29 := rfl\n")
    fresh = run([str(lean), *flags, "Use.lean"], "fresh-after-change")
    if fresh.strip() != b"29":
        raise SystemExit("plain import did not observe the modified dependency")
    run(helper, "build-snapshots-after")
    cached = run([str(lean), *flags, "--incr-load=" + str(snap), "Use.lean"], "cached-after-change")
    if cached != fresh:
        raise SystemExit("header snapshot returned stale semantics")
    if identity(lean) != binary_before:
        raise SystemExit("lean executable identity changed; this did not isolate import invalidation")
    result = {"status": "passed", "lean_identity": binary_before,
              "artifact_sha256_before": artifact_before, "artifact_sha256_after": artifact_after,
              "snapshot_identity_changed": identity(snap) != snap_before,
              "claim": "actual helper plus loader observes changed imported artifact with fixed lean identity"}
    (work / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
