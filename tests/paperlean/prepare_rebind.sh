# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that a workspace's binding of a pack of the cache serves a file only while the file has the
# identity that it had when `paperlean prepare` found its contents to be those packed: a file that is
# written again, even with the same bytes, is read from disk (and its module runs in the interpreter),
# with the same results; `prepare` then binds it again without packing anything.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN
ROOT="$(cd "$TMP_DIR" && pwd -P)"
mkdir -p "$ROOT/ws/dep/Dep"
cd "$ROOT/ws"
cat > dep/lakefile.toml <<'END'
name = "dep"
defaultTargets = ["Dep"]
[[lean_lib]]
name = "Dep"
END
printf 'def base (n : Nat) : Nat := n + 1\n' > dep/Dep/Base.lean
printf 'import Dep.Base\ndef top (n : Nat) : Nat := base n * 2\n' > dep/Dep/Top.lean
printf 'import Dep.Top\n' > dep/Dep.lean
cat > lakefile.toml <<'END'
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "dep"
path = "dep"
[[lean_lib]]
name = "Root"
END
cat > Root.lean <<'END'
import Dep
import Lean.PaperLean.OLeanPack
#eval top 20
#eval show IO Unit from do
  let (served, notServed) ← Lean.PaperLean.OLeanPack.stats
  IO.println s!"served from packs: {served}, read from disk: {notServed}"
END
run lake build Dep
capture lake lean Root.lean
grep -v "^served from packs" "$CAPTURED.out.produced" > "$TMP_DIR/plain.out"

# The files served from packs and read from disk, and the output without those counts.
use() {
  capture env PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean Root.lean
  { grep -v "^paperlean-\|^served from packs" "$CAPTURED.out.produced" || true; } | $DIFF -- "$TMP_DIR/plain.out" - ||
    fail "the prepared data changes the output ($1)"
  served=$(sed -n 's/^served from packs: \([0-9]*\), read from disk: \([0-9]*\)$/\1/p' "$CAPTURED.out.produced")
  disk=$(sed -n 's/^served from packs: \([0-9]*\), read from disk: \([0-9]*\)$/\2/p' "$CAPTURED.out.produced")
}

capture lake paperlean prepare -j 2
check_out_contains "Packing dep"
use "after prepare"
[ "$disk" = 0 ] || fail "files of the dependency were read from disk: $disk"
all=$served

# Dep.Base's `.olean` written again with its own bytes: a new identity, so it is read from disk, and
# with it the other files of its part of the module.
f=dep/.lake/build/lib/lean/Dep/Base.olean
cp "$f" "$TMP_DIR/base.olean"
chmod u+w "$f"
cat "$TMP_DIR/base.olean" > "$f"
use "after a file was written again"
[ "$disk" -gt 0 ] || fail "the file written again was served from the pack"
[ "$served" -lt "$all" ] || fail "as many files served as before: $served"
capture lake paperlean status
check_out_matches "package dep: prepared: pack dep-[0-9a-f]+ of the cache \([0-9]+ modules, 1 changed since and read from disk\)"

# `prepare` binds it again: its bytes are those of the pack, which stays.
capture lake paperlean prepare -j 2
! grep -q "Packing\|Compiling" "$CAPTURED.out.produced" || fail "prepare packed or compiled again"
use "after prepare bound the file again"
[ "$disk" = 0 ] && [ "$served" = "$all" ] || fail "not all files served again: $served of $all, $disk from disk"
capture lake paperlean status
check_out_matches "package dep: prepared: pack dep-[0-9a-f]+ of the cache \([0-9]+ modules\)"
