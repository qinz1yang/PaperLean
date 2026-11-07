#!/usr/bin/env python3
"""Build/run the actual-source P02 regression. All outputs stay under --work.

Example: python3 tests/paperlean/v023_native_snapshot.py --source-root . \
  --build-dir build/release/stage1 --lean build/release/stage1/bin/lean \
  --leanc build/release/stage1/bin/leanc --work /tmp/v023-native-candidate
Use --native-source <baseline>/src/paperlean/native_libs.cpp for the baseline run.
No production source is rewritten, and the snapshot guard is not reproduced in this test.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source-root", type=Path, required=True)
    p.add_argument("--build-dir", type=Path, required=True)
    p.add_argument("--lean", type=Path, required=True)
    p.add_argument("--leanc", type=Path, required=True)
    p.add_argument("--native-source", type=Path)
    p.add_argument("--work", type=Path, required=True)
    p.add_argument("--cxx", default="clang++")
    p.add_argument("--cxx-flag", action="append", default=[])
    a = p.parse_args()
    if platform.system() not in ("Darwin", "Linux"):
        raise SystemExit("P02 gate requires the actual macOS/Linux loader")
    root, build, work = (x.resolve() for x in (a.source_root, a.build_dir, a.work))
    source = (a.native_source or root / "src/paperlean/native_libs.cpp").resolve()
    lean, leanc = str(a.lean.resolve()), str(a.leanc.resolve())
    fixtures = Path(__file__).resolve().parent
    work.mkdir(parents=True, exist_ok=True)
    if any(work.iterdir()):
        raise SystemExit("--work must be empty; logs from a previous run are never overwritten")
    env = {k: v for k, v in os.environ.items() if not k.startswith("PAPERLEAN_")}
    for key in ("LEAN_OLEAN_PACK", "LEAN_IMPORT_IMAGE", "ELAN_TOOLCHAIN", "LEAN_PATH", "LEAN_SYSROOT"):
        env.pop(key, None)
    env["ASAN_OPTIONS"] = "detect_leaks=0:abort_on_error=1"
    env["UBSAN_OPTIONS"] = "halt_on_error=1:print_stacktrace=1"
    # Keep the actual loader thread/concurrency and every ASan check, but run Lean's main
    # on the process main thread. On macOS, the optional lthread wrapper's alternate
    # signal-stack teardown otherwise fails inside ASan after all target assertions.
    case_env = dict(env, LEAN_MAIN_USE_THREAD="0")
    (work / "inputs.json").write_text(json.dumps({"source": str(source),
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "build_headers": str(build), "lean": lean, "leanc": leanc,
        "case_environment": {"LEAN_MAIN_USE_THREAD": "0", "ASAN_OPTIONS": env["ASAN_OPTIONS"]}}, indent=2) + "\n")
    commands = []

    def run(args, label, *, call_env=env):
        commands.append(args)
        proc = subprocess.run(args, cwd=work, env=call_env, capture_output=True, timeout=180)
        (work / (label + ".stdout")).write_bytes(proc.stdout)
        (work / (label + ".stderr")).write_bytes(proc.stderr)
        (work / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
        if proc.returncode:
            raise SystemExit(f"{label} failed ({proc.returncode}); see {work}")

    # Use the selected build's generated private/public headers; no build or cache writes occur.
    includes = [root / "src", build, build / "include", build / "paperlean/include"]
    flags = ["-std=c++17", "-DLEAN_MMAP", "-DLEAN_MULTI_THREAD", "-DLEAN_EXPORTING", "-g", "-O1",
             "-fsanitize=address,undefined", "-fno-omit-frame-pointer", "-pthread"]
    flags += ["-I" + str(path) for path in includes] + a.cxx_flag
    flags += ["-DPAPERLEAN_VERSION=" + json.dumps((root / "paperlean/VERSION").read_text().strip())]
    flags += ["-DV023_NATIVE_LIBS_SOURCE=" + json.dumps(str(source))]
    run([a.cxx, *flags, "-c", str(fixtures / "v023_native_snapshot.cpp"),
         "-o", str(work / "harness.o")], "compile-harness")
    run([lean, "--root=" + str(fixtures), "-c", str(work / "main.c"), str(fixtures / "v023_native_snapshot.lean")], "compile-lean")
    run([leanc, "-c", str(work / "main.c"), "-o", str(work / "main.o")], "compile-main")
    # Use one C++ driver for the instrumented translation unit and its ASan link runtime.
    link_env = dict(env, LEAN_CC=a.cxx)
    run([leanc, "-o", str(work / "native-snapshot"), str(work / "main.o"),
         str(work / "harness.o"), "-fsanitize=address,undefined", "-pthread"], "link", call_env=link_env)
    (work / "later.cpp").write_text(
        'extern "C" __attribute__((visibility("default"))) void initialize_V023Later() {}\n')
    shared = "-dynamiclib" if platform.system() == "Darwin" else "-shared"
    run([a.cxx, shared, "-fPIC", str(work / "later.cpp"), "-o", str(work / "later.so")], "library")
    # 0 catches the empty-vector read; word catches an allocation boundary; 1 also exercises the
    # initializer-owner guard when a bad bit read could otherwise lie inside allocated padding.
    for size in ("0", "word", "1"):
        run([str(work / "native-snapshot"), str(work / "later.so"), size], "case-" + size, call_env=case_env)
    receipt = {"source": str(source), "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
               "platform": platform.platform(), "cases": ["0", "word", "1"],
               "asan": True, "ubsan": True, "main_execution": "process main thread (LEAN_MAIN_USE_THREAD=0)",
               "status": "passed actual verify/load barrier"}
    (work / "result.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt))


if __name__ == "__main__":
    main()
