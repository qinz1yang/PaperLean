#!/usr/bin/env python3
"""S38 release gate using the selected package's real binaries, never development stubs.

mac-unsandboxed checks packaged tools and kernel rejection only, with the CLI's explicit unsafe
flag. linux-sandbox requires real bubblewrap and exercises its actual Lake invocation. Neither mode
silently skips missing binaries. The Linux mode must be run on Linux; a macOS result is not sandbox
evidence. --expected-sha256 may bind this inventory to separately trusted release metadata.
"""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess


TOOLS = ("lean", "lake", "leanexport", "leanchecker", "leanchecker-paranoid",
         "lean4lean", "nanoda_bin", "con-leche", "con-ron")
KERNELS = ("Lean paranoid", "lean4lean", "nanoda", "con-leche", "con-ron", "Lean default")
BINARY_MAGICS = {b"\x7fELF", b"\xcf\xfa\xed\xfe", b"\xfe\xed\xfa\xcf",
                b"\xce\xfa\xed\xfe", b"\xfe\xed\xfa\xce", b"\xca\xfe\xba\xbe",
                b"\xbe\xba\xfe\xca", b"\xca\xfe\xba\xbf", b"\xbf\xba\xfe\xca"}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--sysroot", type=Path, required=True)
    p.add_argument("--mode", choices=("mac-unsandboxed", "linux-sandbox"), required=True)
    p.add_argument("--work", type=Path, required=True)
    p.add_argument("--bwrap", type=Path)
    p.add_argument("--expected-sha256", type=Path,
                   help="trusted release JSON mapping each TOOLS basename to its SHA256")
    p.add_argument("--provenance", type=Path,
                   help="JSON mapping tool basenames to origin records (candidate build or pinned release)")
    a = p.parse_args()
    required_platform = "Darwin" if a.mode == "mac-unsandboxed" else "Linux"
    if platform.system() != required_platform:
        raise SystemExit(f"{a.mode} requires {required_platform}; this host cannot validate that gate")
    sysroot, work = a.sysroot.resolve(), a.work.resolve()
    work.mkdir(parents=True, exist_ok=True)
    if any(work.iterdir()):
        raise SystemExit("--work must be empty")
    expected = json.loads(a.expected_sha256.read_text()) if a.expected_sha256 else None
    provenance = json.loads(a.provenance.read_text()) if a.provenance else {}
    inventory, unavailable = {}, []
    for tool in TOOLS:
        path = sysroot / "bin" / tool
        if not path.is_file() or not os.access(path, os.X_OK):
            unavailable.append(tool + ": missing executable")
            continue
        try:
            path.resolve().relative_to(sysroot)
        except ValueError:
            unavailable.append(tool + ": resolves outside the selected package")
            continue
        with path.open("rb") as handle:
            magic = handle.read(4)
        if magic not in BINARY_MAGICS:
            unavailable.append(tool + ": not a native executable (scripts/stubs are excluded)")
            continue
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        inventory[tool] = {"path": str(path), "resolved": str(path.resolve()), "sha256": digest,
                           "origin": provenance.get(tool, "selected prefix; origin not separately supplied")}
        if expected is not None and expected.get(tool) != digest:
            unavailable.append(tool + ": does not match the trusted package digest")
    (work / "inventory.json").write_text(json.dumps(inventory, indent=2) + "\n")
    if unavailable:
        (work / "blocked.json").write_text(json.dumps({"missing_or_invalid": unavailable}, indent=2) + "\n")
        raise SystemExit("packaged-checker gate blocked: " + "; ".join(unavailable))
    env = {k: v for k, v in os.environ.items() if not k.startswith("PAPERLEAN_")}
    for key in ("LEAN_OLEAN_PACK", "LEAN_IMPORT_IMAGE", "ELAN_TOOLCHAIN", "LAKE_OVERRIDE_LEAN",
                "LEAN_SYSROOT", "LEAN_PATH", "COMPARATOR_BWRAP", "LAKE_CHECK_EXPORT"):
        env.pop(key, None)
    env["PATH"] = str(sysroot / "bin") + os.pathsep + env.get("PATH", "")
    env["LEAN_ABORT_ON_PANIC"] = "1"
    unsafe = ["--inadvisably-no-sandbox"] if a.mode == "mac-unsandboxed" else []
    bwrap_record = None
    if a.mode == "linux-sandbox":
        bwrap = a.bwrap or (Path(shutil.which("bwrap")) if shutil.which("bwrap") else None)
        if bwrap is None or not bwrap.is_file() or not os.access(bwrap, os.X_OK):
            raise SystemExit("Linux release gate requires installed executable bubblewrap; no fake fallback")
        bwrap = bwrap.resolve()
        with bwrap.open("rb") as handle:
            if handle.read(4) != b"\x7fELF":
                raise SystemExit("Linux release gate rejects shell/fake bubblewrap wrappers")
        env["COMPARATOR_BWRAP"] = str(bwrap)
        bwrap_record = {"path": str(bwrap), "sha256": hashlib.sha256(bwrap.read_bytes()).hexdigest()}
    commands = []

    def run(args, label, expected_rc=0):
        commands.append(args)
        # The full sandbox path exports Init and runs all six kernels sequentially.
        timeout = 3600 if args == [str(sysroot / "bin" / "lake"), "check", "--paranoid"] else 180
        proc = subprocess.run(args, cwd=work, env=env, capture_output=True, timeout=timeout)
        (work / (label + ".stdout")).write_bytes(proc.stdout)
        (work / (label + ".stderr")).write_bytes(proc.stderr)
        (work / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
        if proc.returncode != expected_rc:
            raise SystemExit(f"{label}: expected exit {expected_rc}, got {proc.returncode}; see {work}")
        return proc.stdout + proc.stderr

    lean, exporter, lake = (str(sysroot / "bin" / n) for n in ("lean", "leanexport", "lake"))
    (work / "V023Check.lean").write_text("theorem v023Acceptance : True := True.intro\n")
    run([lean, "-o", "V023Check.olean", "V023Check.lean"], "compile")
    env["LEAN_PATH"] = str(work)
    run([exporter, "V023Check", "--", "v023Acceptance"], "export")
    # Exporter's stderr is retained separately. Only its actual stdout is the input stream.
    exported = (work / "export.stdout").read_bytes()
    (work / "good.export").write_bytes(exported)
    rows = [json.loads(line) for line in exported.decode().splitlines() if line.strip()]
    names = {0: ""}
    for row in rows:
        if "in" in row and "str" in row:
            pre, text = row["str"]["pre"], row["str"]["str"]
            names[row["in"]] = (names[pre] + "." if names[pre] else "") + text
        elif "in" in row and "num" in row:
            pre, number = row["num"]["pre"], row["num"]["i"]
            names[row["in"]] = (names[pre] + "." if names[pre] else "") + str(number)
    bad = copy.deepcopy(rows)
    changed = 0
    for row in bad:
        if "thm" in row and names.get(row["thm"]["name"]) == "v023Acceptance":
            # A valid expression index and valid export syntax, but True : Prop is not a proof
            # of True. This is kernel rejection, not a malformed-file/parser smoke test.
            if row["thm"]["value"] == row["thm"]["type"]:
                raise SystemExit("fixture theorem unexpectedly has identical proof and type")
            row["thm"]["value"] = row["thm"]["type"]
            changed += 1
    if changed != 1:
        raise SystemExit(f"expected exactly one theorem proof mutation, found {changed}")
    (work / "bad.export").write_text("\n".join(json.dumps(r, separators=(",", ":")) for r in bad) + "\n")
    if a.mode == "mac-unsandboxed":
        refused = run([lake, "check", "--paranoid", "--from-export", str(work / "good.export")],
                      "default-sandbox-refused", 2)
        if b"needs Linux namespaces" not in refused:
            raise SystemExit("macOS default mode did not explicitly refuse the unavailable Linux sandbox")
    else:
        # Exercise Lake's real sandboxed build/export path as well as its from-export checker path.
        # This is a small trusted fixture, not an adversarial isolation/security certification.
        (work / "lakefile.toml").write_text(
            'name = "v023-checkers"\ndefaultTargets = ["V023Check"]\n'
            '[[lean_lib]]\nname = "V023Check"\n')
        run([lake, "resolve-deps"], "resolve-fixture")
        built = run([lake, "check", "--paranoid"], "sandbox-build-export")
        for kernel in KERNELS:
            if f"{kernel} kernel accepts the solution".encode() not in built:
                raise SystemExit(f"sandboxed build/export lacks a successful result from {kernel}")
        if b"WARNING: Sandbox disabled" in built:
            raise SystemExit("Linux build/export unexpectedly disabled the sandbox")
    for filename, label, rc, action in (("good.export", "positive", 0, "accepts"),
                                       ("bad.export", "negative", 1, "rejected")):
        output = run([lake, "check", "--paranoid", *unsafe, "--from-export", str(work / filename)], label, rc)
        for kernel in KERNELS:
            expected_line = f"{kernel} kernel {action} the solution".encode()
            if expected_line not in output:
                raise SystemExit(f"{label}: missing individual result from {kernel}; other failures do not count")
        warning = b"WARNING: Sandbox disabled, this run is not trustworthy."
        if (warning in output) != bool(unsafe):
            raise SystemExit("sandbox mode did not match the explicit invocation")
    # Repeat the valid export after rejection to rule out an installation that always fails.
    run([lake, "check", "--paranoid", *unsafe, "--from-export", str(work / "good.export")], "positive-again")
    result = {"status": "passed", "mode": a.mode, "platform": platform.platform(),
              "kernels": KERNELS, "inventory": inventory, "bubblewrap": bwrap_record,
              "trusted_package_digests_checked": expected is not None,
              "negative_case": "one theorem proof replaced by its Prop-valued type expression",
              "sandbox_claim": "real Lake/bubblewrap build/export/checker execution; not a complete sandbox security audit"
                  if a.mode == "linux-sandbox" else "none: explicit macOS unsandboxed checker compatibility only"}
    (work / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
