# PGO and Linux BOLT builds

This recipe builds a new optimized toolchain from pinned inputs. It does not reproduce an
existing release byte for byte: that requires the release's exact compiler/sysroot archives,
dependency checksums, training corpus and driver, profiles, and build options. Keep those
inputs with each new artifact. No signing or upload credentials are needed for these steps.

Use a clean checkout, CMake 3.21 or newer, Make, `shasum`, and the dependencies in the ordinary
build instructions. PGO uses Clang and llvm-profdata from the **same pinned LLVM installation** on
macOS or Linux. Linux BOLT additionally needs matching llvm-bolt/perf2bolt and Linux perf.
Record their versions and archive SHA-256 hashes, the OS/architecture, SDK/sysroot and native
dependency identities, the source commit and stage0 tree, and all configuration arguments.
Use a fresh build directory when any of these inputs changes; sysroot changes are not traced
by all existing build rules. The inherited standalone packaging scripts assume paths without
shell metacharacters; use simple build paths for this recipe.

## Pin the workload

Set `TRAIN` to an executable, versioned training driver and `TRAIN_MANIFEST` to its immutable
corpus/dependency manifest. The driver takes a toolchain directory as its first argument,
invokes that directory's `bin/lean`/`bin/lake`, preserves `LLVM_PROFILE_FILE` for instrumented children, checks every command's exit status, and resets
workload build outputs before each run. It must not select another toolchain through elan or
reuse outputs compiled by a different candidate. Include imports, elaboration, tactics and
compilation representative of the intended use. Keep a separate validation/benchmark workload;
training inputs alone do not establish correctness or an improvement.

For an initial smoke run, a driver can invoke the supplied toolchain's `lean` on a fixed list
of standalone `.lean` files. Publish that list and the file hashes with the driver. A smoke
corpus is not a substitute for the representative workload used to justify a release.

## Build and train PGO

Run in Bash at the checkout root. Set `LLVM_BIN`, `TRAIN`, and `TRAIN_MANIFEST` to absolute
paths and `JOBS` to the intended build parallelism. `WORK` must be a new, nonexistent directory.

```bash
set -euo pipefail
: "${LLVM_BIN:?pinned LLVM bin directory}"
: "${TRAIN:?versioned training driver}"
: "${TRAIN_MANIFEST:?training input manifest}"
: "${JOBS:?build parallelism}"
: "${WORK:?new absolute build directory}"
test ! -e "$WORK"
test -x "$TRAIN"
test -f "$TRAIN_MANIFEST"
SRC=$PWD
mkdir -p "$WORK"/{raw,build-raw}
git rev-parse HEAD > "$WORK/source.commit"
git rev-parse HEAD:stage0 > "$WORK/stage0.tree"
cp "$TRAIN_MANIFEST" "$WORK/training.manifest"
shasum -a 256 "$TRAIN" "$TRAIN_MANIFEST" > "$WORK/training.sha256"
"$LLVM_BIN/clang" --version > "$WORK/compiler.version"
"$LLVM_BIN/clang++" --version > "$WORK/compiler-cxx.version"
"$LLVM_BIN/clang" -print-resource-dir > "$WORK/compiler.resource"
"$LLVM_BIN/clang++" -print-resource-dir > "$WORK/compiler-cxx.resource"
"$LLVM_BIN/llvm-profdata" --version > "$WORK/profdata.version"

# Retain ELF relocations in toolchain executables/shared libraries for the later BOLT step.
RELOCS=""
if [[ $(uname -s) == Linux ]]; then RELOCS="-Wl,--emit-relocs"; fi
BASE_LINK=""
MAC_SDK=""
if command -v lld >/dev/null; then BASE_LINK="-fuse-ld=lld"; fi
if [[ $(uname -s) == Darwin ]]; then
  MAC_SDK=$(xcrun --show-sdk-path)
  BASE_LINK+=" -headerpad_max_install_names"
fi
build_variant() (
  if [[ -n $MAC_SDK ]]; then export SDKROOT="$MAC_SDK"; fi
  local directory=$1 compile_flags=$2 link_flags=$3
  cmake -S "$SRC" -B "$directory" -G 'Unix Makefiles' \
    -DCMAKE_BUILD_TYPE=Release -DSTRIP_BINARIES=OFF -DCCACHE=OFF -DSTAGE0_CCACHE=OFF -DUSE_LAKE=ON -DUSE_LAKE_CACHE=OFF \
    "-DCMAKE_C_COMPILER:FILEPATH=$LLVM_BIN/clang" "-DCMAKE_CXX_COMPILER:FILEPATH=$LLVM_BIN/clang++" \
    "-DLEAN_EXTRA_CXX_FLAGS=$compile_flags" \
    "-DPAPERLEAN_STDLIB_CC_FLAGS=$compile_flags" \
    "-DLEAN_EXTRA_LINKER_FLAGS=$BASE_LINK $link_flags" \
    "-DCMAKE_EXE_LINKER_FLAGS=$RELOCS" "-DTOOLCHAIN_SHARED_LINKER_FLAGS=$RELOCS"
  cmake --build "$directory" --parallel "$JOBS"
)

# Separate profiles produced while building from the intended training profiles.
build="$WORK/build"
LLVM_PROFILE_FILE="$WORK/build-raw/%m-%p.profraw" \
  build_variant "$build" '-fprofile-generate -fprofile-update=atomic' '-fprofile-generate'
LLVM_PROFILE_FILE="$WORK/raw/%m-%p.profraw" "$TRAIN" "$build/stage1"
shopt -s nullglob
raw_profiles=("$WORK/raw/"*.profraw)
test "${#raw_profiles[@]}" -gt 0
printf '%s\n' "${raw_profiles[@]}" > "$WORK/raw.list"
"$LLVM_BIN/llvm-profdata" merge --failure-mode=any --input-files="$WORK/raw.list" -o "$WORK/profile.profdata"
shasum -a 256 "$WORK/profile.profdata" > "$WORK/profile.sha256"

# Profile-use is a compile option; no profiling runtime/link flag is needed in this build.
mv "$build" "$WORK/generate-receipt"
build_variant "$build" "-fprofile-use=$WORK/profile.profdata" ''
ctest --test-dir "$build/stage1" --output-on-failure
cmake --build "$build" --target check-stage3 --parallel "$JOBS"
cmake --install "$build" --prefix "$WORK/pgo"
"$TRAIN" "$WORK/pgo"
```

Both passes use the same absolute build path so LLVM can match file-local functions in
generated C. The moved tree is a receipt; do not use it to build again. Inspect consumed
counters for exercised functions in generated C and C++. Stage2/3 are a fixed-point check;
their generated source paths differ from the trained stage1.
Keep the configure/build logs and both stage1 `CMakeCache.txt` files. Inspect profile mismatch
or missing-profile diagnostics; resolve unexpected mismatches rather than suppressing them.
`PAPERLEAN_STDLIB_CC_FLAGS` confines generated-C profiling options to Lean's own libraries.
Do not publish the instrumented build. These steps follow LLVM's
[instrumentation PGO workflow](https://clang.llvm.org/docs/UsersManual.html#profiling-with-instrumentation).

The commands above produce host builds. A standalone macOS package additionally needs a pinned
dependency/sysroot configuration. When adapting that configuration, capture preparation's exit
status before consuming its options; merge platform and PGO linker flags rather than overwriting
either. This is the checked preparation/configuration pattern, not another PGO build command:

```bash
(
  mkdir "$WORK/standalone"
  cd "$WORK/standalone"
  llvm_options=$("$SRC/script/prepare-llvm-macos.sh" "$TARGET_LLVM_ARCHIVE") || exit
  eval "cmake -S \"$SRC\" -B . $llvm_options"
)
```

Use the absolute archive path. For an instrumented standalone build, include the matching
`libclang_rt.profile_osx.a` in the prepared stage1 Clang resource directory and append
the generator link flag to the prepared platform flags. Record the archive hashes and GMP/libuv/OpenSSL/SDK identities. Host-built output does not
establish portability to another machine or minimum OS version.

## Apply BOLT on Linux

Preserve the PGO installation and collect from a separate candidate copy. Set `BOLT_OBJECT`
to a relative ELF image path selected from the recorded profile, for example
`lib/lean/libleanshared.so`. Lean's shared libraries contain substantial executable code;
optimizing `bin/lean` alone does not cover those libraries. Repeat conversion/optimization
for each selected image, retaining a manifest of its original hash, profile and output hash.

Run the copy and collection once, before rewriting any image:

```bash
test "$(uname -s)" = Linux
cp -a "$WORK/pgo" "$WORK/bolt"
mkdir "$WORK/bolt-profiles"
"$LLVM_BIN/llvm-bolt" --version > "$WORK/bolt.version"
perf --version > "$WORK/perf.version"
perf record -e cycles:u -j any,u -o "$WORK/perf.data" -- "$TRAIN" "$WORK/bolt"
```

Then run this block once per selected original image, using distinct receipt/profile names:

```bash
: "${BOLT_OBJECT:?relative path of the ELF executable or shared library to optimize}"
image="$WORK/bolt/$BOLT_OBJECT"
record="$WORK/bolt-profiles/${BOLT_OBJECT//\//_}"
test ! -e "$record.input.sha256"
"$LLVM_BIN/llvm-readelf" --sections "$image" > "$record.sections"
grep -q '\.rela.text' "$record.sections"
shasum -a 256 "$image" > "$record.input.sha256"
"$LLVM_BIN/perf2bolt" "$image" -p "$WORK/perf.data" -o "$record.fdata"
"$LLVM_BIN/llvm-bolt" "$image" -o "$image.bolt" -data="$record.fdata" \
  -reorder-blocks=ext-tsp -reorder-functions=cdsort -split-functions -split-all-cold \
  -split-eh -dyno-stats
chmod --reference="$image" "$image.bolt"
shasum -a 256 "$record.fdata" "$image.bolt" > "$record.output.sha256"
mv "$image.bolt" "$image"
"$TRAIN" "$WORK/bolt"
```

Require a nonempty profile for the intended image and inspect BOLT's relocation/profile
diagnostics. Never apply a profile to a different input image. If the machine cannot collect
the selected branch events, stop and choose a documented sampling method supported by that
LLVM/CPU combination; record the change. See the primary
[BOLT instructions](https://github.com/llvm/llvm-project/blob/main/bolt/README.md) for ELF
requirements, shared-library support and sampling conversion.

## Validate and package

Run the full required test/checker suite with the **final installed candidate**, including
kernel/export checks, Lake/package builds, process/async IO, LSP and an FFI compilation/link.
Repeat smoke tests after moving the entire installation to a different directory, and on the
minimum supported OS/sysroot. A PGO build's pre-BOLT tests do not validate rewritten ELF images.
Keep an unoptimized reference built from the same source and pinned dependencies. Benchmark
both on the same host with fresh outputs and the same workload; publish measurements only
after these gates pass, without attributing a gain to an unmeasured optimization.

Package only the verified installation, excluding raw profiles, build caches and local logs.
Store beside it a receipt with the source/upstream and stage0 identities, compiler/dependency
locks, complete options, training/validation driver and corpus identities, merged profile hash,
per-image BOLT identities, final file/archive hashes, and actual validation commands/results.
Keep debug images before stripping; stripping or signing changes bytes and needs its own final
hash and smoke check. Publishing/signing is a separate release operation.


The compatibility test, `paperlean/olean_compat.sh`, gives official rc3 only
the public `.olean` files from an accelerated build and checks a downstream
proof. To investigate generated C, IR and native ABI differences, configure a
stage with `-DPAPERLEAN_COMPARE_UPSTREAM_NATIVE=ON` and run
`ctest -L upstream-native-comparison`. Those comparisons are diagnostic.
