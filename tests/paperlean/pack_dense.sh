# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests the dense copies that a pack records for import (`pack_header::dense_*`, `pack_part::dense_*`,
# `pack_edge::name_copy`, `pack_ext_entry::entries_copy`): a pack of `Init` records them, the fast
# import uses the pack, its results are those of the legacy import (`PAPERLEAN_IMPORT=check` compares
# the maps and module graph), and the dense copies are inside the recorded area.

LIB="$(lean --print-libdir)"
ROOT="$TMP_DIR/lib"
# A private copy of `Init`: packs record the identity of their files.
(cd "$LIB" && find Init Init.* -type f ! -name '*.hash' \( -name '*.olean*' -o -name '*.ir' -o -name '*.ir.sig' \)) |
  while read -r f; do
    mkdir -p "$ROOT/$(dirname "$f")"
    cp "$LIB/$f" "$ROOT/$f"
  done

cat > "$TMP_DIR/pack.lean" <<'EOF'
import Lean.PaperLean.OLeanPack
def main (args : List String) : IO Unit := do
  let n ← Lean.PaperLean.OLeanPack.create #[args[1]!] args[0]!
  IO.println s!"packed: {decide (n > 0)}"
EOF
capture lean --run "$TMP_DIR/pack.lean" "$TMP_DIR/init.paperlean" "$ROOT"
check_out_contains "packed: true"

cat > "$TMP_DIR/header.lean" <<'EOF'
import Lean.PaperLean.OLeanPack
open Lean.PaperLean
def word (b : ByteArray) (off : Nat) : UInt64 := Id.run do
  let mut w : UInt64 := 0
  for i in [0:8] do
    w := w ||| (b[off + i]!.toUInt64 <<< (8 * i).toUInt64)
  return w
def main (args : List String) : IO Unit := do
  let b ← (← IO.FS.Handle.mk args[0]! .read).read 424
  let format := (word b 152) >>> 32   -- `olean_flags`, then `format`
  let numEntries := word b 184
  let rootsOff := word b 328
  let namesOff := word b 336
  let entriesOff := word b 176
  let denseOff := word b 408
  let denseSize := word b 416
  IO.println s!"format: {format}"
  IO.println s!"dense area: {decide (denseSize > 0)} {decide (denseOff >= namesOff)} {decide (denseOff + denseSize <= entriesOff)}"
  IO.println s!"entries: {decide (numEntries > 0 ∧ rootsOff > 4096)}"
EOF
capture lean --run "$TMP_DIR/header.lean" "$TMP_DIR/init.paperlean"
check_out_contains "format: 9"
check_out_contains "dense area: true true true"
check_out_contains "entries: true"

cat > "$TMP_DIR/test.lean" <<'EOF'
import Init
#check @Nat.add_comm
#eval (List.range 100).foldl (· + ·) 0
theorem t (xs : List Nat) : (xs ++ []).length = xs.length := by simp
#print axioms t
EOF
capture env LEAN_PATH="$ROOT" lean "$TMP_DIR/test.lean"
cp "$CAPTURED.out.produced" "$TMP_DIR/plain.out"
capture env LEAN_PATH="$ROOT" LEAN_OLEAN_PACK="$TMP_DIR/init.paperlean" PAPERLEAN_IMPORT_TIMING=1 lean "$TMP_DIR/test.lean"
check_out_contains "paperlean-timing modules.fast"
grep -v "^paperlean-" "$CAPTURED.out.produced" > "$TMP_DIR/packed.out"
$DIFF -- "$TMP_DIR/plain.out" "$TMP_DIR/packed.out" || fail "output differs when import reads the dense copies"
capture env LEAN_PATH="$ROOT" LEAN_OLEAN_PACK="$TMP_DIR/init.paperlean" PAPERLEAN_IMPORT=check lean "$TMP_DIR/test.lean"
check_out_contains "Nat.add_comm"
$DIFF -- "$TMP_DIR/plain.out" "$CAPTURED.out.produced" || fail "PAPERLEAN_IMPORT=check differs from the plain import"

# The dense copies do not make a changed file acceptable: the pack's own freshness check still
# reads the file's identity.
cp "$ROOT/Init/Core.olean" "$TMP_DIR/Core.olean"
rm "$ROOT/Init/Core.olean"
mv "$TMP_DIR/Core.olean" "$ROOT/Init/Core.olean"
capture env LEAN_PATH="$ROOT" LEAN_OLEAN_PACK="$TMP_DIR/init.paperlean" PAPERLEAN_IMPORT_TIMING=1 lean "$TMP_DIR/test.lean"
check_out_contains "paperlean-timing modules.fallback"
grep -v "^paperlean-" "$CAPTURED.out.produced" > "$TMP_DIR/changed.out"
$DIFF -- "$TMP_DIR/plain.out" "$TMP_DIR/changed.out" || fail "output differs after changing a packed file"
