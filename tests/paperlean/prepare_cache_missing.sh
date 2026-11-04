# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that prepared data whose entries of the cache are gone (deleted, or purged with the cache
# directory) is not used, with the same results: Lean warns and reads the package's files from disk,
# and runs its modules in the interpreter; `paperlean status` says why; `paperlean prepare` writes the
# entries again.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN
ROOT="$(cd "$TMP_DIR" && pwd -P)"
CACHE="$PAPERLEAN_CACHE_DIR/prepared"
mkdir -p "$ROOT/ws/dep/Dep"
cd "$ROOT/ws"
cat > dep/lakefile.toml <<'END'
name = "dep"
defaultTargets = ["Dep"]
[[lean_lib]]
name = "Dep"
END
printf 'def base (n : Nat) : Nat := n + 1\n' > dep/Dep/Base.lean
cat > dep/Dep/Twice.lean <<'END'
import Lean
macro "twice! " x:term : term => `($x + $x)
END
printf 'import Dep.Base\nimport Dep.Twice\n' > dep/Dep.lean
cat > lakefile.toml <<'END'
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "dep"
path = "dep"
[[lean_lib]]
name = "Root"
END
printf 'import Dep\n#eval twice! base 20\n' > Root.lean
run lake build Dep
capture lake lean Root.lean
cp "$CAPTURED.out.produced" "$TMP_DIR/plain.out"

# The output with the prepared data, its warnings apart, and the native libraries that it used.
use() {
  capture env PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean Root.lean
  { grep -v "^paperlean-\|^warning: " "$CAPTURED.out.produced" || true; } | $DIFF -- "$TMP_DIR/plain.out" - ||
    fail "the prepared data changes the output ($1)"
}

capture lake paperlean prepare -j 2
use "prepared"
check_out_matches "paperlean-timing native libs=1 "
! grep -q "^warning" "$CAPTURED.out.produced" || fail "warnings with the prepared data: $(grep "^warning" "$CAPTURED.out.produced")"

# The pack is gone: the binding, and the image of the packs, are not used.
rm -rf "$CACHE"/*/pack/dep-*
use "without the pack"
check_out_matches "warning: ignoring olean pack '.*/bind/dep-[0-9a-f]+\.paperlean': its pack '.*/pack/dep-[0-9a-f]+/pack\.paperlean': "
check_out_contains "it belongs to other olean packs than those of LEAN_OLEAN_PACK"
check_out_matches "paperlean-timing native libs=0 "
capture lake paperlean status
check_out_matches "package dep: prepared: its pack dep-[0-9a-f]+ is not used \(.*\); run \`paperlean prepare\`"
check_out_matches "pack\.paperlean: missing"

# The library is gone too.
rm -rf "$CACHE"/*/native/dep-*
use "without the pack and the library"
check_out_matches "warning: ignoring native library manifest '.*/native/dep-[0-9a-f]+/dep\.paperlean': cannot be read"
capture lake paperlean status
check_out_matches "its native library dep-[0-9a-f]+ is missing from the cache; run \`paperlean prepare\`"

# The whole cache is gone (as a system that purges caches deletes it).
rm -rf "$PAPERLEAN_CACHE_DIR"
use "without the cache"
check_out_contains "warning: ignoring olean pack"

# `prepare` writes the entries again.
capture lake paperlean prepare -j 2
check_out_contains "Packing dep"
check_out_contains "Compiling the native library of dep"
use "prepared again"
check_out_matches "paperlean-timing native libs=1 "
! grep -q "^warning" "$CAPTURED.out.produced" || fail "warnings with the data prepared again"
