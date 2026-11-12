# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests the faster construction of imported simp sets and instances (`importedState?` in
# `ScopedEnvExtension.addImportedFn`): under `PAPERLEAN_IMPORT=check` the state is built both ways and
# compared, for imports whose fold erases theorems, replaces equal values and updates the same keys
# from several modules, in several orders; an import image that changed since it was written, or
# whose tables are damaged (found by checksums), is ignored with a warning without changing results.
# Images are read-only.

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
# Check mode finds a defect of the states built faster.
capture_fail env LEAN_PATH="$LIB" PAPERLEAN_IMPORT=check PAPERLEAN_IMPORT_CHECK_FAULT=state lean UseA.lean
check_out_contains "PAPERLEAN_IMPORT=check: the imported state of"

# With an olean pack of the modules and an import image of it, the entries of packed modules are
# replayed from the image; `Init`'s are not in the pack. Import timing shows that the image is read
# and has the simp set and the instances (and its tables are checked where they are used, below).
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
      PAPERLEAN_IMPORT="$mode" PAPERLEAN_IMPORT_TIMING=1 lean "$name.lean"
    for ext in simpExtension instanceExtension; do
      check_out_matches "^paperlean-counter prefetch\.[a-zA-Z]+ ext=Lean\.Meta\.$ext"
    done
    { grep -v "^paperlean-" "$CAPTURED.out.produced" || true; } | $DIFF -- "$TMP_DIR/$name.legacy.out" - ||
      fail "output of $name differs from the legacy import with the image ($mode)"
  done
done
capture env LEAN_PATH="$LIB" LEAN_OLEAN_PACK="$TMP_DIR/s.paperlean" PAPERLEAN_IMPORT_TIMING=1 lean UseA.lean
! grep -q "^paperlean-counter prefetch" "$CAPTURED.out.produced" || fail "the image was consulted without LEAN_IMPORT_IMAGE"

# A large simp set (`Init`'s) is replayed on another thread from the start of
# `finalizePersistentExtensions`. The image describes the packs that it was written with, here only the
# first, so the entries of a module in a second pack are replayed by calling Lean functions, also after
# that pack is rebuilt with other entries.
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
    capture env LEAN_PATH="$LIB1:$LIB2" LEAN_OLEAN_PACK="$TMP_DIR/p1.paperlean" lean --run "$TMP_DIR/image.lean" \
      "$TMP_DIR/p.image.paperlean"
    check_out_contains "image: true"
    case "$(uname -s)" in
      Darwin|Linux)
        fixture="$TEST_DIR/paperlean/replay_ownership"
        gmp_args=()
        if grep -q '^USE_GMP:BOOL=ON$' "$BUILD_DIR/CMakeCache.txt"; then
          gmp_include=$(sed -n 's/^GMP_INCLUDE_DIR:PATH=//p' "$BUILD_DIR/CMakeCache.txt")
          gmp_args+=(-DLEAN_USE_GMP "-I$gmp_include")
        fi
        version=$(cat "$SRC_DIR/../paperlean/VERSION")
        run ${CXX:-c++} -std=c++20 -DLEAN_MULTI_THREAD -DLEAN_MMAP "-DPAPERLEAN_VERSION=\"$version\"" \
          -I"$SRC_DIR" -I"$BUILD_DIR/include" -I"$BUILD_DIR" -I"$BUILD_DIR/paperlean/include" \
          "${gmp_args[@]}" -c "$fixture/counted.cpp" -o "$TMP_DIR/replay_counted.o"
        run lean --root="$fixture" -c "$TMP_DIR/replay_counted.c" "$fixture/Replay.lean"
        # The probe imports modules and interprets their code, like a `lean_exe` with `supportInterpreter :=
        # true`: the interpreter must find the executable's own symbols, which on Linux needs `-rdynamic`
        # (macOS exports them by default)
        RDYNAMIC=; [ "$(uname -s)" = Linux ] && RDYNAMIC=-rdynamic
        run leanc ${LEANC_OPTS-} $RDYNAMIC -o "$TMP_DIR/replay_counted" "$TMP_DIR/replay_counted.c" "$TMP_DIR/replay_counted.o"
        run env LEAN_PATH="$LIB1:$LIB2" LEAN_OLEAN_PACK="$PACKS" LEAN_IMPORT_IMAGE="$TMP_DIR/p.image.paperlean" \
          PAPERLEAN_IMPORT_THREADS=4 "$TMP_DIR/replay_counted" "$(lean --print-prefix)" S6
        ;;
    esac
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

# An image of another pack, or one written to since it was written, is ignored.
cp "$TMP_DIR/s.image.paperlean" "$TMP_DIR/bad.image.paperlean"
chmod u+w "$TMP_DIR/bad.image.paperlean"
printf 'X' | dd of="$TMP_DIR/bad.image.paperlean" bs=1 seek=$(($(wc -c < "$TMP_DIR/bad.image.paperlean") - 1)) conv=notrunc 2>/dev/null
capture env LEAN_PATH="$LIB" LEAN_OLEAN_PACK="$TMP_DIR/s.paperlean" LEAN_IMPORT_IMAGE="$TMP_DIR/bad.image.paperlean" lean UseA.lean
check_out_contains "warning: ignoring import image"
check_out_contains "it changed since it was written"
grep -v "warning: ignoring" "$CAPTURED.out.produced" | $DIFF -- "$TMP_DIR/UseA.legacy.out" - ||
  fail "output of UseA differs with a changed image"
capture env LEAN_PATH="$LIB" LEAN_IMPORT_IMAGE="$TMP_DIR/s.image.paperlean" lean UseA.lean
check_out_contains "warning: ignoring import image"

# Lean checks the parts of the tables of an image that has its writer's modification time when it
# first uses them, by their checksums and bounds: damaged tables (here, damaged with that time
# restored) are not used, with a warning, and results do not change. `damage_tables <name> <field>
# <size>` sets the table at offset `<field>` of every extension's record (`image_ext` in
# `src/paperlean/import_state.cpp`), of elements of `<size>` bytes, to 0xff.
damaged_image() {
  touch -r "$TMP_DIR/s.image.paperlean" "$TMP_DIR/$1.image.paperlean"
  for name in UseA UseB UseC; do
    capture env LEAN_PATH="$LIB" LEAN_OLEAN_PACK="$TMP_DIR/s.paperlean" LEAN_IMPORT_IMAGE="$TMP_DIR/$1.image.paperlean" lean "$name.lean"
    check_out_contains "warning: ignoring the import image's tables"
    grep -v "warning: ignoring" "$CAPTURED.out.produced" | $DIFF -- "$TMP_DIR/$name.legacy.out" - ||
      fail "output of $name differs with damaged $1"
  done
}
damage_tables() {
  cp "$TMP_DIR/s.image.paperlean" "$TMP_DIR/$1.image.paperlean"
  chmod u+w "$TMP_DIR/$1.image.paperlean"
  perl -e '
    open(F, "+<", $ARGV[0]) or die; binmode F;
    read(F, my $h, 224); my $n = unpack("L", substr($h, 156, 4)); my $exts = unpack("Q", substr($h, 184, 8));
    for my $i (0 .. $n - 1) {
      seek(F, $exts + $i * 272 + $ARGV[1], 0); read(F, my $r, 16); my ($off, $num) = unpack("QQ", $r);
      seek(F, $off, 0); print F "\xff" x ($ARGV[2] * $num);
    }
    close F' "$TMP_DIR/$1.image.paperlean" "$2" "$3"
  damaged_image "$1"
}
# the steps of entries (`image_step`), and the index of name classes
damage_tables steps 248 16
damage_tables names 168 4
# within bounds: the first instance (`image_entry` of kind 3) with a name gets the next name class
cp "$TMP_DIR/s.image.paperlean" "$TMP_DIR/class.image.paperlean"
chmod u+w "$TMP_DIR/class.image.paperlean"
perl -e '
  open(F, "+<", $ARGV[0]) or die; binmode F;
  read(F, my $h, 224); my $n = unpack("L<", substr($h, 156, 4)); my $exts = unpack("Q<", substr($h, 184, 8));
  EXT: for my $i (0 .. $n - 1) {
    seek(F, $exts + $i * 272, 0); read(F, my $x, 272);
    next unless unpack("L<", substr($x, 16, 4)) == 1;
    my ($names, $off, $num) = (unpack("Q<", substr($x, 160, 8)), unpack("Q<Q<", substr($x, 232, 16)));
    for my $j (0 .. $num - 1) {
      seek(F, $off + 56 * $j, 0); read(F, my $e, 56);
      my $cls = unpack("L<", substr($e, 24, 4));
      next unless ord($e) == 3 && $cls != 0xffffffff && $names > 1;
      seek(F, $off + 56 * $j + 24, 0); print F pack("L<", ($cls + 1) % $names);
      last EXT;
    }
  }
  close F' "$TMP_DIR/class.image.paperlean"
damaged_image class
# `verifyImportImage` reads all tables
cat > "$TMP_DIR/verify.lean" <<'END'
import Lean.PaperLean.OLeanPack
def main (args : List String) : IO Unit := do
  for a in args do IO.println s!"{a}: [{← Lean.PaperLean.OLeanPack.verifyImportImage a}]"
END
capture lean --run "$TMP_DIR/verify.lean" "$TMP_DIR/s.image.paperlean" "$TMP_DIR/steps.image.paperlean" "$TMP_DIR/bad.image.paperlean"
check_out_contains "$TMP_DIR/s.image.paperlean: []"
check_out_contains "$TMP_DIR/steps.image.paperlean: [corrupt"
check_out_contains "$TMP_DIR/bad.image.paperlean: [it changed since it was written]"

[ "$(stat -c %a "$TMP_DIR/s.image.paperlean" 2>/dev/null || stat -f %Lp "$TMP_DIR/s.image.paperlean")" = 444 ] ||
  fail "the image is not read-only"
