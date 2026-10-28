# Tests the faster implementations of `importModules` steps (`PAPERLEAN_IMPORT`): imports give
# the same results and errors with and without them, and `PAPERLEAN_IMPORT=check`, which builds the
# imported state both ways and compares the objects, finds no difference.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK
SRC="$TMP_DIR/src"
LIB="$TMP_DIR/lib"
mkdir -p "$SRC" "$LIB"

# `A` and `B` prove the same theorem; the later one in import order replaces the earlier one,
# while `const2ModIdx` keeps the first module. `C` defines a different constant of the same name.
cat > "$SRC/A.lean" <<'EOF'
theorem t : 1 = 1 := rfl
def a := 1
EOF
cat > "$SRC/B.lean" <<'EOF'
theorem t : 1 = 1 := Eq.refl 1
def b := 2
EOF
cat > "$SRC/C.lean" <<'EOF'
def t : Nat := 3
EOF
cd "$SRC"
for m in A B C; do
  run lean -o "$LIB/$m.olean" "$m.lean"
done

cat > "$SRC/UseAB.lean" <<'EOF'
import Lean
import A
import B
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  IO.println s!"module of t: {(env.getModuleIdxFor? `t).map (env.header.moduleNames[·]!)}"
#print t
#check a + b
EOF
cat > "$SRC/UseAC.lean" <<'EOF'
import A
import C
EOF

for mode in "" legacy check; do
  capture env LEAN_PATH="$LIB" PAPERLEAN_IMPORT="$mode" lean UseAB.lean
  check_out_contains "Eq.refl 1"
  check_out_contains "module of t: (some A)"
  cp "$CAPTURED.out.produced" "$TMP_DIR/ab.$mode.out"
  capture_fail env LEAN_PATH="$LIB" PAPERLEAN_IMPORT="$mode" lean UseAC.lean
  check_out_contains "import C failed, environment already contains 't' from A"
  cp "$CAPTURED.out.produced" "$TMP_DIR/ac.$mode.out"
done
for f in ab ac; do
  $DIFF -- "$TMP_DIR/$f..out" "$TMP_DIR/$f.legacy.out" || fail "output of $f differs from the legacy import"
  $DIFF -- "$TMP_DIR/$f..out" "$TMP_DIR/$f.check.out" || fail "output of $f differs under PAPERLEAN_IMPORT=check"
done

# A larger import: `Lean` itself, compared object by object.
cat > "$SRC/UseLean.lean" <<'EOF'
import Lean
#check Lean.Environment
EOF
capture env PAPERLEAN_IMPORT=check lean UseLean.lean
check_out_contains "Lean.Environment : Type"

# The mode is really selected: only the fast constant maps report their step.
capture env PAPERLEAN_IMPORT=legacy PAPERLEAN_IMPORT_TIMING=1 lean UseLean.lean
if grep -q "paperlean-timing constants.fast.build" "$CAPTURED.out.produced"; then
  fail "PAPERLEAN_IMPORT=legacy used the fast constant maps"
fi
capture env PAPERLEAN_IMPORT_TIMING=1 lean UseLean.lean
check_out_contains "paperlean-timing constants.fast.build"
capture env PAPERLEAN_IMPORT=check PAPERLEAN_IMPORT_TIMING=1 lean UseLean.lean
check_out_contains "paperlean-timing constants.fast.build"

# With an olean pack, the constant maps take the names' hashes from the pack's name tables and skip
# the search for an equal key where the tables rule one out. `A` and `B` are packed, `C` is read from
# disk; imported before `A`, its `t` must still be found to clash with `A`'s.
PACKED="$TMP_DIR/packed"
UNPACKED="$TMP_DIR/unpacked"
mkdir -p "$PACKED" "$UNPACKED"
cp "$LIB/A.olean" "$LIB/B.olean" "$PACKED/"
cp "$LIB/C.olean" "$UNPACKED/"
# usage: pack.lean <out> <root> [base address]; packs used together need disjoint addresses
cat > "$TMP_DIR/pack.lean" <<'EOF2'
import Lean.PaperLean.OLeanPack
def main (args : List String) : IO Unit := do
  let base := (args[2]?.bind String.toNat?).getD 0x200000000000
  let n ← Lean.PaperLean.OLeanPack.create #[args[1]!] args[0]! (baseAddr := base.toUSize)
  IO.println s!"packed: {n}"
EOF2
capture lean --run "$TMP_DIR/pack.lean" "$TMP_DIR/ab.paperlean" "$PACKED"
check_out_contains "packed: 2"
cat > "$SRC/UseCA.lean" <<'EOF2'
import C
import A
EOF2
for mode in "" legacy check; do
  capture env LEAN_PATH="$PACKED:$UNPACKED" LEAN_OLEAN_PACK="$TMP_DIR/ab.paperlean" PAPERLEAN_IMPORT="$mode" lean UseAB.lean
  $DIFF -- "$TMP_DIR/ab..out" "$CAPTURED.out.produced" || fail "output of ab differs with the pack ($mode)"
  capture_fail env LEAN_PATH="$PACKED:$UNPACKED" LEAN_OLEAN_PACK="$TMP_DIR/ab.paperlean" PAPERLEAN_IMPORT="$mode" lean UseAC.lean
  $DIFF -- "$TMP_DIR/ac..out" "$CAPTURED.out.produced" || fail "output of ac differs with the pack ($mode)"
  capture_fail env LEAN_PATH="$PACKED:$UNPACKED" LEAN_OLEAN_PACK="$TMP_DIR/ab.paperlean" PAPERLEAN_IMPORT="$mode" lean UseCA.lean
  check_out_contains "import A failed, environment already contains 't' from C"
done

# Several packs over the same root: a file is served by the first pack with a root that is a prefix
# of its path, or read from disk if that pack lacks it, even when a later pack has it. `a.paperlean`
# has only `A`; `B` must be read from disk, not from `ab.paperlean`.
LATE="$TMP_DIR/late"
mkdir -p "$LATE"
cp "$LIB/A.olean" "$LATE/"
capture lean --run "$TMP_DIR/pack.lean" "$TMP_DIR/a.paperlean" "$LATE"
check_out_contains "packed: 1"
cp "$LIB/B.olean" "$LATE/"
capture lean --run "$TMP_DIR/pack.lean" "$TMP_DIR/late-ab.paperlean" "$LATE" $((0x210000000000))
check_out_contains "packed: 2"
for mode in "" check; do
  capture env LEAN_PATH="$LATE" LEAN_OLEAN_PACK="$TMP_DIR/a.paperlean:$TMP_DIR/late-ab.paperlean" PAPERLEAN_IMPORT="$mode" lean UseAB.lean
  $DIFF -- "$TMP_DIR/ab..out" "$CAPTURED.out.produced" || fail "output of ab differs with two packs ($mode)"
done

# A package found in two pack roots: the search path decides which root the import reads, for each
# module of the package. `P.X` lies in the first root, `P.Y` only in the second, which the search
# path does not use for `P`.
mkdir -p "$SRC/P" "$TMP_DIR/r1/P" "$TMP_DIR/r2/P"
echo 'def x := 1' > "$SRC/P/X.lean"
echo 'def y := 2' > "$SRC/P/Y.lean"
run lean -o "$TMP_DIR/r1/P/X.olean" P/X.lean
run lean -o "$TMP_DIR/r2/P/Y.olean" P/Y.lean
capture lean --run "$TMP_DIR/pack.lean" "$TMP_DIR/r1.paperlean" "$TMP_DIR/r1"
capture lean --run "$TMP_DIR/pack.lean" "$TMP_DIR/r2.paperlean" "$TMP_DIR/r2" $((0x210000000000))
cat > "$SRC/UseP.lean" <<'EOF2'
import P.X
import P.Y
EOF2
capture_fail env LEAN_PATH="$TMP_DIR/r1:$TMP_DIR/r2" lean UseP.lean
cp "$CAPTURED.out.produced" "$TMP_DIR/p.out"
for mode in "" check; do
  capture_fail env LEAN_PATH="$TMP_DIR/r1:$TMP_DIR/r2" LEAN_OLEAN_PACK="$TMP_DIR/r1.paperlean:$TMP_DIR/r2.paperlean" PAPERLEAN_IMPORT="$mode" lean UseP.lean
  $DIFF -- "$TMP_DIR/p.out" "$CAPTURED.out.produced" || fail "output of UseP differs with packs ($mode)"
done
