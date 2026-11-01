# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests incremental snapshots (`--incr-save`, `--incr-load`) of a file whose imports are served from
# an olean pack: a snapshot saved after loading one loads, also several times over, as without the
# pack (the `CompactedRegion`s of packed files have their roots inside their regions).

LIB="$TMP_DIR/lib"
mkdir -p "$LIB"
cd "$TMP_DIR"

cat > pack.lean <<'END'
import Lean.PaperLean.OLeanPack
def main (args : List String) : IO Unit := do
  let n ← Lean.PaperLean.OLeanPack.create #[args[1]!] args[0]!
  IO.println s!"packed: {decide (n > 0)}"
END
echo 'def a := 1' > A.lean
printf 'import A\ndef b := a + 1\n' > B.lean
printf 'import B\n#eval b + 1\n' > S.lean
for m in A B; do run env LEAN_PATH="$LIB" lean -o "$LIB/$m.olean" $m.lean; done
capture lean --run pack.lean "$TMP_DIR/n.paperlean" "$LIB"
check_out_contains "packed: true"

capture env LEAN_PATH="$LIB" LEAN_OLEAN_PACK="$TMP_DIR/n.paperlean" lean --incr-save=1.snap S.lean
check_out_contains "3"
for i in 1 2 3; do
  capture env LEAN_PATH="$LIB" LEAN_OLEAN_PACK="$TMP_DIR/n.paperlean" \
    lean --incr-load=$i.snap --incr-save=$((i + 1)).snap S.lean
  check_out_contains "3"
done
# (the regions of the imports are embedded as they are, not copied)
size1=$(wc -c < 1.snap); size4=$(wc -c < 4.snap)
[ "$size4" -le $((size1 + size1 / 10)) ] || fail "the snapshot grew from $size1 to $size4 bytes"
