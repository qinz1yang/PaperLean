# Tests the faster construction of imported simp sets and instances (`importedState?` in
# `ScopedEnvExtension.addImportedFn`): under `PAPERLEAN_IMPORT=check` the state is built both ways and
# compared, for imports whose fold erases theorems, replaces equal values and updates the same keys
# from several modules, in several orders.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK
SRC="$TMP_DIR/src"
LIB="$TMP_DIR/lib"
mkdir -p "$SRC" "$LIB"
cd "$SRC"

cat > S1.lean <<'END'
theorem foo (n : Nat) : n + 0 = n := Nat.add_zero n
attribute [simp] foo
@[simp] def double (n : Nat) : Nat := 2 * n
@[reducible] def triple (n : Nat) : Nat := 3 * n
attribute [simp] triple
instance (priority := low) i1 : Inhabited Nat := ⟨1⟩
theorem bar (xs : List Nat) : xs ++ [] = xs := List.append_nil xs
attribute [simp] bar
END
cat > S2.lean <<'END'
import S1
-- the backward direction: importing `S1` then `S2` erases the forward `foo`
attribute [simp ←] foo
-- the same instance value with another priority replaces the leaf value
instance (priority := high) i2 : Inhabited Nat := i1
theorem bar' (xs : List Nat) : xs ++ [] = xs := List.append_nil xs
attribute [simp] bar'
END
cat > S3.lean <<'END'
import S2
-- the forward direction again, erasing the backward one
attribute [simp] foo
@[simp] theorem double_eq (n : Nat) : double n = n + n := by unfold double; omega
END
cat > S4.lean <<'END'
@[simp] theorem baz (n : Nat) : 0 + n = n := Nat.zero_add n
instance i4 : Inhabited Nat := ⟨4⟩
END
for m in S1 S2 S3 S4; do
  run env LEAN_PATH="$LIB" lean -o "$LIB/$m.olean" "$m.lean"
done

cat > UseA.lean <<'END'
import Lean
import S3
import S4
open Lean Meta in
#eval show MetaM Unit from do
  let thms ← getSimpTheorems
  IO.println s!"{thms.isLemma (.decl ``bar)} {thms.isLemma (.decl ``bar')} {thms.isLemma (.decl ``baz)}"
  IO.println s!"{thms.isDeclToUnfold ``triple} {thms.toUnfoldThms.contains ``double}"
#eval (default : Nat)
example (n : Nat) : 0 + n = n := by simp
END
cat > UseB.lean <<'END'
import Lean
import S4
import S2
import S1
open Lean Meta in
#eval show MetaM Unit from do
  let thms ← getSimpTheorems
  IO.println s!"foo forward: {thms.isLemma (.decl ``foo)}, backward: {thms.isLemma (.decl ``foo (inv := true))}"
#eval (default : Nat)
END
cat > UseC.lean <<'END'
import Lean
import S3
open Lean Meta in
#eval show MetaM Unit from do
  let thms ← getSimpTheorems
  IO.println s!"foo forward: {thms.isLemma (.decl ``foo)}, backward: {thms.isLemma (.decl ``foo (inv := true))}"
  IO.println s!"erased: {thms.erased.contains (.decl ``foo)} {thms.erased.contains (.decl ``foo (inv := true))}"
END

for name in UseA UseB UseC; do
  capture env LEAN_PATH="$LIB" PAPERLEAN_IMPORT=legacy lean "$name.lean"
  cp "$CAPTURED.out.produced" "$TMP_DIR/$name.legacy.out"
  for mode in "" check; do
    capture env LEAN_PATH="$LIB" PAPERLEAN_IMPORT="$mode" lean "$name.lean"
    $DIFF -- "$TMP_DIR/$name.legacy.out" "$CAPTURED.out.produced" ||
      fail "output of $name differs from the legacy import ($mode)"
  done
done
check_out_contains "foo forward: true, backward: false"

# With an olean pack of the modules and an import image of it, the entries of packed modules are
# replayed from the image; `Init`'s are not in the pack.
cat > "$TMP_DIR/pack.lean" <<'END'
import Lean.PaperLean.OLeanPack
def main (args : List String) : IO Unit := do
  let n ← Lean.PaperLean.OLeanPack.create #[args[1]!] args[0]!
  IO.println s!"packed: {n}"
END
capture lean --run "$TMP_DIR/pack.lean" "$TMP_DIR/s.paperlean" "$LIB"
check_out_contains "packed: 4"
cat > "$TMP_DIR/image.lean" <<'END'
import Lean.PaperLean.ImportState
def main (args : List String) : IO Unit := do
  let n ← Lean.PaperLean.writeImportImage args[0]!
  IO.println s!"image: {decide (n > 0)}"
END
capture env LEAN_OLEAN_PACK="$TMP_DIR/s.paperlean" lean --run "$TMP_DIR/image.lean" "$TMP_DIR/s.image.paperlean"
check_out_contains "image: true"
for name in UseA UseB UseC; do
  for mode in "" check; do
    capture env LEAN_PATH="$LIB" LEAN_OLEAN_PACK="$TMP_DIR/s.paperlean" LEAN_IMPORT_IMAGE="$TMP_DIR/s.image.paperlean" \
      PAPERLEAN_IMPORT="$mode" lean "$name.lean"
    $DIFF -- "$TMP_DIR/$name.legacy.out" "$CAPTURED.out.produced" ||
      fail "output of $name differs from the legacy import with the image ($mode)"
  done
done

# A large simp set (`Init`'s) is replayed on another thread from the start of
# `finalizePersistentExtensions`. The image describes only the first pack, so the entries of a
# module in a second pack are replayed by calling Lean functions, also after that pack is rebuilt
# with other entries.
LIB1="$TMP_DIR/lib1"
LIB2="$TMP_DIR/lib2"
mkdir -p "$LIB1" "$LIB2"
# a copy, not hard links: a new link changes the ctime of the toolchain's files, which other tests
# record in their packs
LEANLIB="$(lean --print-libdir)"
(cd "$LEANLIB" && find Init Init.* -type f \( -name '*.olean*' -o -name '*.ir' -o -name '*.ir.sig' \)) |
  while read -r f; do
    mkdir -p "$LIB1/$(dirname "$f")"
    cp "$LEANLIB/$f" "$LIB1/$f"
  done
cat > S5.lean <<'END'
def g (n : Nat) : Nat := n + 1
@[simp] theorem g_succ (n : Nat) : g (n + 1) = g n + 1 := rfl
END
run env LEAN_PATH="$LIB1" lean -o "$LIB1/S5.olean" S5.lean
cat > S6.lean <<'END'
import S5
@[simp] theorem g_zero : g 0 = 1 := rfl
END
cat > UseD.lean <<'END'
import S6
example : g 2 = 3 := by simp
END
cat > "$TMP_DIR/pack2.lean" <<'END'
import Lean.PaperLean.OLeanPack
def main (args : List String) : IO Unit := do
  let base : USize := if args[2]? == some "2" then 0x210000000000 else 0x200000000000
  let n ← Lean.PaperLean.OLeanPack.create #[args[1]!] args[0]! base
  IO.println s!"packed: {decide (n > 0)}"
END
capture lean --run "$TMP_DIR/pack2.lean" "$TMP_DIR/p1.paperlean" "$LIB1" 1
check_out_contains "packed: true"
PACKS="$TMP_DIR/p1.paperlean:$TMP_DIR/p2.paperlean"
for round in 1 2; do
  run env LEAN_PATH="$LIB1:$LIB2" lean -o "$LIB2/S6.olean" S6.lean
  capture lean --run "$TMP_DIR/pack2.lean" "$TMP_DIR/p2.paperlean" "$LIB2" 2
  check_out_contains "packed: true"
  if [ "$round" = 1 ]; then
    capture env LEAN_PATH="$LIB1:$LIB2" LEAN_OLEAN_PACK="$PACKS" lean --run "$TMP_DIR/image.lean" "$TMP_DIR/p.image.paperlean"
    check_out_contains "image: true"
  fi
  # `UseD` succeeds in round 1, while `g_zero` is a simp lemma, and fails in round 2
  capture_only "" env LEAN_PATH="$LIB1:$LIB2" PAPERLEAN_IMPORT=legacy lean UseD.lean
  LEGACY_EXIT=$EXIT
  if [ "$round" = 1 ]; then check_exit_is_success; else check_exit_is_fail; fi
  cp "$CAPTURED.out.produced" "$TMP_DIR/UseD.legacy.out"
  for mode in "" check; do
    capture_exit "$LEGACY_EXIT" env LEAN_PATH="$LIB1:$LIB2" LEAN_OLEAN_PACK="$PACKS" LEAN_IMPORT_IMAGE="$TMP_DIR/p.image.paperlean" \
      PAPERLEAN_IMPORT="$mode" PAPERLEAN_IMPORT_TIMING=1 lean UseD.lean
    grep -q "prefetch.started ext=Lean.Meta.simpExtension" "$CAPTURED.out.produced" ||
      fail "the default simp set is not prefetched (round $round, $mode)"
    { grep -v "^paperlean-" "$CAPTURED.out.produced" || true; } | $DIFF -- "$TMP_DIR/UseD.legacy.out" - ||
      fail "output of UseD differs from the legacy import with two packs (round $round, $mode)"
  done
  # the second pack's module changes; the image, which describes the first pack, stays usable
  perl -pi -e 's/^\@\[simp\] theorem g_zero/theorem g_zero/' S6.lean
done

# An image of another pack, or a damaged one, is ignored.
cp "$TMP_DIR/s.image.paperlean" "$TMP_DIR/bad.image.paperlean"
printf 'X' | dd of="$TMP_DIR/bad.image.paperlean" bs=1 seek=$(($(wc -c < "$TMP_DIR/bad.image.paperlean") - 1)) conv=notrunc 2>/dev/null
capture env LEAN_PATH="$LIB" LEAN_OLEAN_PACK="$TMP_DIR/s.paperlean" LEAN_IMPORT_IMAGE="$TMP_DIR/bad.image.paperlean" lean UseA.lean
check_out_contains "warning: ignoring the import image's tables"
grep -v "warning: ignoring" "$CAPTURED.out.produced" | $DIFF -- "$TMP_DIR/UseA.legacy.out" - ||
  fail "output of UseA differs with a damaged image"
capture env LEAN_PATH="$LIB" LEAN_IMPORT_IMAGE="$TMP_DIR/s.image.paperlean" lean UseA.lean
check_out_contains "warning: ignoring import image"
