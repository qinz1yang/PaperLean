#!/usr/bin/env python3
"""Run S37's actual compiler/helper gate, then test warm reuse and incomplete cache states.

Requires v023_header_snapshot.py from the preceding acceptance packet beside this driver.
Every mutation is confined to the explicitly supplied empty --work directory.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source-root", type=Path, required=True)
    p.add_argument("--lean", type=Path, required=True)
    p.add_argument("--work", type=Path, required=True)
    a = p.parse_args()
    root, lean, work = (path.resolve() for path in (a.source_root, a.lean, a.work))
    work.mkdir(parents=True, exist_ok=True)
    if any(work.iterdir()):
        raise SystemExit("--work must be empty")
    fixture = work / "fixture"
    gate = Path(__file__).with_name("v023_header_snapshot.py")
    commands = []

    def run(args, label, *, env=None, cwd=work, success=True):
        commands.append(args)
        proc = subprocess.run(args, cwd=cwd, env=env, capture_output=True, timeout=180)
        (work / (label + ".stdout")).write_bytes(proc.stdout)
        (work / (label + ".stderr")).write_bytes(proc.stderr)
        (work / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
        if (proc.returncode == 0) != success:
            raise SystemExit(f"{label}: unexpected exit {proc.returncode}; see {work}")
        return proc.stdout

    run([sys.executable, str(gate), "--source-root", str(root), "--lean", str(lean),
         "--work", str(fixture)], "artifact-change")
    env = {k: v for k, v in os.environ.items() if not k.startswith("PAPERLEAN_")}
    for key in ("LEAN_OLEAN_PACK", "LEAN_IMPORT_IMAGE", "ELAN_TOOLCHAIN", "LEAN_SYSROOT"):
        env.pop(key, None)
    env.update(PATH=str(lean.parent) + os.pathsep + env.get("PATH", ""), LEAN_PATH=str(fixture / "lib"),
               LEAN_HEADER_SNAPSHOT_LEAN=str(fixture / "lean.snap"),
               LEAN_HEADER_SNAPSHOT_INIT=str(fixture / "init.snap"))
    snapshots = [fixture / "lean.snap", fixture / "init.snap"]
    outputs = [Path(str(path) + suffix) for path in snapshots for suffix in ("", ".deps")]
    receipt = fixture / "lean.snap.receipt.json"
    helper = ["bash", str(root / "tests/build_lean_header_snapshots.sh")]

    def ids(paths):
        return [(s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
                for s in (p.stat() for p in paths)]

    def verify(label, expected=b"29", cwd=fixture):
        out = run([str(lean), "-DprintMessageEndPos=true", "-Dlinter.all=false", "-DElab.inServer=true",
                   "--incr-load=" + str(snapshots[0]), "Use.lean"], label, env=env, cwd=cwd)
        if out.strip() != expected:
            raise SystemExit(label + ": stale or missing semantics")

    before = ids(outputs + [receipt])
    run(helper, "warm", env=env, cwd=fixture)
    if ids(outputs + [receipt]) != before:
        raise SystemExit("warm invocation rewrote the completed snapshot pair")
    for case in ("missing-receipt", "corrupt-receipt", "corrupt-deps", "incomplete-pair"):
        if case == "missing-receipt":
            receipt.unlink()
        elif case == "corrupt-receipt":
            receipt.write_text("{broken receipt")
        elif case == "corrupt-deps":
            Path(str(snapshots[0]) + ".deps").write_text("{broken dependencies")
        else:
            # State left by interruption before both pairs and the completion receipt exist.
            receipt.unlink()
            snapshots[1].unlink()
        before_pair = ids([snapshots[0]])
        run(helper, case, env=env, cwd=fixture)
        if ids([snapshots[0]]) == before_pair or not all(p.is_file() for p in outputs + [receipt]):
            raise SystemExit(case + ": did not rebuild a complete pair")
        verify(case + "-semantics")
    artifact = fixture / "lib/V023SnapshotDep.olean"
    saved, mode = artifact.read_bytes(), artifact.stat().st_mode & 0o777
    artifact.unlink()
    try:
        run(helper, "missing-artifact", env=env, cwd=fixture, success=False)
        if receipt.exists() or any(p.exists() for p in outputs):
            raise SystemExit("failed rebuild left stale snapshots or a completion receipt")
    finally:
        artifact.write_bytes(saved)
        artifact.chmod(mode)
    run(helper, "restored-artifact", env=env, cwd=fixture)
    verify("restored-semantics")

    # The explicit earlier root precedes the old library. The empty last component is retained
    # too: Lean joins "" / "Pkg" as /Pkg, not as a current-directory PATH shorthand.
    earlier = work / "earlier"
    earlier.mkdir()
    (earlier / "Use.lean").write_bytes((fixture / "Use.lean").read_bytes())
    env["LEAN_PATH"] = os.pathsep.join([str(earlier), str(fixture / "lib"), ""])
    run(helper, "earlier-empty", env=env, cwd=earlier)
    verify("earlier-empty-semantics", cwd=earlier)
    before = ids(outputs + [receipt])
    run(helper, "custom-warm", env=env, cwd=earlier)
    if ids(outputs + [receipt]) != before:
        raise SystemExit("stable custom namespace did not reuse its completed pair")
    # Publish a new top-level V023SnapshotDep.olean in that previously empty earlier root; do
    # not change any artifact recorded by the old pair. The namespace witness must detect it.
    old_files = sorted({(earlier / p).absolute() for snap in snapshots
                        for row in json.loads(Path(str(snap) + ".deps").read_text()) for p in row.values()})
    old_ids = ids(old_files)
    source = work / "shadow-source"
    source.mkdir()
    (source / "V023SnapshotDep.lean").write_text(
        "def v023SnapshotValue : Nat := 47\ndef v023SnapshotFresh : Nat := 47\n")
    shadow = earlier / "V023SnapshotDep.olean"
    run([str(lean), "-o", str(shadow), "V023SnapshotDep.lean"], "compile-earlier-shadow", env=env, cwd=source)
    (earlier / "Use.lean").write_text(
        "import Lean\n#eval v023SnapshotValue\nexample : v023SnapshotFresh = 47 := rfl\n")
    fresh = run([str(lean), "-DprintMessageEndPos=true", "-Dlinter.all=false", "-DElab.inServer=true",
                 "Use.lean"], "plain-shadow", env=env, cwd=earlier)
    if fresh.strip() != b"47" or ids(old_files) != old_ids:
        raise SystemExit("shadow fixture did not isolate changed routing with stable old artifacts")
    run(helper, "repair-shadow", env=env, cwd=earlier)
    verify("cached-shadow", b"47", earlier)
    recorded = json.loads(Path(str(snapshots[0]) + ".deps").read_text())
    # A relative dependency path is resolved against the producer/consumer working directory.
    selected = {str((earlier / p).absolute()) for row in recorded for p in row.values()}
    if str(shadow) not in selected or str(artifact) in selected or ids(old_files) != old_ids:
        raise SystemExit("rebuilt snapshot did not select only the earlier shadow artifact")
    # findWithExt also chooses a root from a directory alone. Introducing an empty Lean/
    # must now make `import Lean` fail there, not reuse the old later-root snapshot by mistake.
    (earlier / "Lean").mkdir()
    run(helper, "directory-shadows-missing-olean", env=env, cwd=earlier, success=False)
    if receipt.exists() or any(p.exists() for p in outputs):
        raise SystemExit("directory-only shadow left stale snapshots available")
    (earlier / "Lean").rmdir()
    run(helper, "restore-directory-shadow", env=env, cwd=earlier)
    verify("restore-directory-shadow-semantics", b"47", earlier)
    result = {"status": "passed", "cases": ["changed-artifact", "warm-reuse", "missing-receipt",
              "corrupt-receipt", "corrupt-deps", "incomplete-pair", "missing-artifact", "restored-artifact",
              "stable-custom-warm", "earlier-shadow-olean", "earlier-shadow-directory"],
              "interruption_scope": "constructed incomplete publication state; no real process-kill injection"}
    (work / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
