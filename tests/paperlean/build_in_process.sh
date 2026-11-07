# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that `paperlean build` builds in its own process (`runBuild` in
# `src/lake/Lake/PaperLean/Cli.lean`, `PaperLean.buildIn` in `src/lake/Lake/CLI/Main.lean`) with the
# variables that a Lake of its own would have, and starts a Lake of its own where the build's arguments
# would load the workspace otherwise: here a build that packs (forced) packs in the directory of the
# process that builds; either way the same files, and the same exit codes for a failing build and for
# `--no-build`.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN PAPERLEAN_DATA PAPERLEAN_BUILD_PACKS PAPERLEAN_BUILD_PACKS_KEEP PAPERLEAN_ACCELERATE
export XDG_CACHE_HOME="$(cd "$TMP_DIR" && pwd -P)/cache"
WS="$(cd "$TMP_DIR" && pwd -P)/ws"
mkdir -p "$WS/Root"
cd "$WS"
cat > lakefile.toml <<'END'
name = "root"
defaultTargets = ["Root"]
[[lean_lib]]
name = "Root"
END
printf 'def a : Nat := 1\n' > Root/A.lean
printf 'import Root.A\ndef b : Nat := a + 1\n' > Root/B.lean
printf 'import Root.B\n' > Root.lean
outputs() { (cd "$WS" && find .lake/build -name '*.olean*' -o -name '*.ilean' -o -name '*.c' -o -name '*.trace' | sort); }

run lake build
for f in $(outputs); do mkdir -p "$TMP_DIR/ref/$(dirname "$f")"; cp "$f" "$TMP_DIR/ref/$f"; done
same_files() {
  for f in $(outputs); do cmp -s "$f" "$TMP_DIR/ref/$f" || fail "$f differs from plain lake's"; done
}

# `paperlean build` with arguments that load the workspace as it does: the build packs in its own
# directory, that of the `lake paperlean` process.
rm -rf .lake/build
PAPERLEAN_BUILD_PACKS=1 PAPERLEAN_BUILD_PACKS_KEEP=1 lake paperlean build > "$TMP_DIR/out" 2>&1 &
pid=$!
wait $pid || { cat "$TMP_DIR/out"; fail "paperlean build failed"; }
cat "$TMP_DIR/out"
has_pid_packdir() {
  for d in ".lake/paperlean/build/$1"-*; do [ ! -d "$d" ] || return 0; done
  return 1
}
has_pid_packdir "$pid" || fail "the build did not run in the paperlean process: $(ls .lake/paperlean/build)"
[ "$(grep -c "Build completed successfully" "$TMP_DIR/out")" = 1 ] || fail "not one build"
same_files

# With an option that reconfigures, a Lake of its own builds. (Without the packs of the builds above,
# which would pass for those of this one.)
rm -rf .lake/build .lake/paperlean/build
PAPERLEAN_BUILD_PACKS=1 PAPERLEAN_BUILD_PACKS_KEEP=1 lake paperlean build -R > "$TMP_DIR/out" 2>&1 &
pid=$!
wait $pid || { cat "$TMP_DIR/out"; fail "paperlean build -R failed"; }
cat "$TMP_DIR/out"
! has_pid_packdir "$pid" || fail "the build with -R ran in the paperlean process"
[ -n "$(ls .lake/paperlean/build 2>/dev/null)" ] || fail "the build with -R did not pack"
same_files

# Targets and options of `lake build`, and its exit codes.
rm -rf .lake/build
capture lake paperlean build Root.A -q
! grep -q "Built" "$CAPTURED.out.produced" || fail "-q reported built modules"
[ -f .lake/build/lib/lean/Root/A.olean ] && [ ! -f .lake/build/lib/lean/Root/B.olean ] ||
  fail "not the target Root.A alone"
printf 'import Root.A\ndef b : Nat := "no"\n' > Root/B.lean
capture_exit 1 lake paperlean build
check_out_contains "Root.B"
capture_exit 3 lake paperlean build --no-build
printf 'import Root.A\ndef b : Nat := a + 1\n' > Root/B.lean
capture_exit 3 lake paperlean build --no-build
capture_exit 1 lake paperlean build no-such-target
run lake paperlean build
same_files

# Preparing after the build, in the same process.
capture lake paperlean build --prepare
check_out_contains "Nothing is prepared yet; preparing everything."
capture lake paperlean status
check_out_contains "used: "
