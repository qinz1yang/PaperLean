# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests native libraries of packages (`PAPERLEAN_NATIVE_LIBS`, `src/paperlean/native_libs.cpp`): an
# import uses a library's native code only for imported modules served from an olean pack whose
# files are those of the library's manifest, and the output is that of interpreting them; the module
# being compiled is interpreted; changed, shadowed or damaged inputs disable the library.

cp native_helper.lean "$TMP_DIR/"
SRC="$TMP_DIR/src"
LIB="$TMP_DIR/lib"
mkdir -p "$SRC" "$LIB"
cd "$SRC"

cat > N1.lean <<'END'
def nf (n : Nat) : Nat := n * 2 + 1
initialize nref : IO.Ref Nat ← IO.mkRef 41
#eval nf 3
END
cat > N2.lean <<'END'
import N1
def ng (n : Nat) : Nat := nf n + 100
END
# A second import in the same process; the first environment's imported declarations, whose
# initializers ran natively, keep using the native code.
cat > UseN.lean <<'END'
import Lean
import N2
#eval ng 5
open Lean in
#eval show IO Unit from do
  (unsafe enableInitializersExecution : IO Unit)
  let h ← IO.getNumHeartbeats
  let env ← importModules #[{ module := `N2 }] {} (leakEnv := true) (loadExts := true)
  -- an import counts no heartbeats
  IO.println s!"imported again: {env.contains `ng}, heartbeats: {decide ((← IO.getNumHeartbeats) - h < 1000)}"
#eval show IO Nat from do return (← nref.get) + 1
#eval (List.range 1000).foldl (fun a n => a + nf n) 0
END

cat > "$TMP_DIR/pack.lean" <<'END'
import Lean.PaperLean.OLeanPack
def main (args : List String) : IO Unit := do
  let n ← Lean.PaperLean.OLeanPack.create #[args[1]!] args[0]!
  IO.println s!"packed: {decide (n > 0)}"
END

# Compiles modules to `.olean` (and `.c` with `-c`) files.
compile() {
  local c=0
  if [[ "$1" == -c ]]; then c=1; shift; fi
  for m in "$@"; do
    if [[ $c == 1 ]]; then
      run env LEAN_PATH="$LIB" lean -o "$LIB/$m.olean" -i "$LIB/$m.ilean" -c "$TMP_DIR/$m.c" $m.lean
    else
      run env LEAN_PATH="$LIB" lean -o "$LIB/$m.olean" -i "$LIB/$m.ilean" $m.lean
    fi
  done
}
# link <library> <module>...
link() {
  local lib=$1; shift
  local cs=()
  for m in "$@"; do cs+=("$TMP_DIR/$m.c"); done
  run leanc -shared -DLEAN_EXPORTING -o "$lib" "${cs[@]}"
}
# manifest <manifest> <library> <module>...
manifest() {
  capture env LEAN_PATH="$LIB" lean --run "$TMP_DIR/native_helper.lean" manifest "$1" "$2" "$TMP_DIR" "${@:3}"
  check_out_contains "manifest written"
}
pack() {
  capture lean --run "$TMP_DIR/pack.lean" "$TMP_DIR/n.paperlean" "$LIB"
  check_out_contains "packed: true"
}
# expect <file> <expected output>: the output of `lean <file>` without the timing lines
expect_output() {
  { grep -v "^paperlean-" "$CAPTURED.out.produced" || true; } | $DIFF -- "$2" - || fail "output of $1 differs: $3"
}
NATIVE=(LEAN_OLEAN_PACK="$TMP_DIR/n.paperlean" PAPERLEAN_NATIVE_LIBS="$TMP_DIR/libn.paperlean" PAPERLEAN_IMPORT_TIMING=1)

compile -c N1 N2
link "$TMP_DIR/libn.so" N1 N2
manifest "$TMP_DIR/libn.paperlean" "$TMP_DIR/libn.so" N1 N2
pack
capture env LEAN_PATH="$LIB" lean UseN.lean
check_out_contains "111"
check_out_contains "imported again: true, heartbeats: true"
cp "$CAPTURED.out.produced" "$TMP_DIR/UseN.expected"
capture env LEAN_PATH="$LIB" "${NATIVE[@]}" lean UseN.lean
check_out_contains "paperlean-timing native libs=1 modules=2"
expect_output UseN "$TMP_DIR/UseN.expected" "with the native library"
# `check` compares with the legacy import, which reads the packed files from the pack as well
capture env LEAN_PATH="$LIB" "${NATIVE[@]}" PAPERLEAN_IMPORT=check lean UseN.lean
check_out_contains "paperlean-timing native libs=1 modules=2"
expect_output UseN "$TMP_DIR/UseN.expected" "in check mode"
capture env LEAN_PATH="$LIB" "${NATIVE[@]}" PAPERLEAN_IMPORT=legacy lean UseN.lean
expect_output UseN "$TMP_DIR/UseN.expected" "in legacy mode"
# without the pack, the modules cannot be verified
capture env LEAN_PATH="$LIB" PAPERLEAN_NATIVE_LIBS="$TMP_DIR/libn.paperlean" PAPERLEAN_IMPORT_TIMING=1 lean UseN.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
# A damaged manifest is ignored with a warning; a valid one after it is still used.
cp "$TMP_DIR/libn.paperlean" "$TMP_DIR/bad.paperlean"
printf 'X' | dd of="$TMP_DIR/bad.paperlean" bs=1 seek=$(($(wc -c < "$TMP_DIR/bad.paperlean") - 1)) conv=notrunc 2>/dev/null
capture env LEAN_PATH="$LIB" "${NATIVE[@]}" PAPERLEAN_NATIVE_LIBS="$TMP_DIR/bad.paperlean:$TMP_DIR/libn.paperlean" lean UseN.lean
check_out_contains "warning: ignoring native library manifest '$TMP_DIR/bad.paperlean'"
check_out_contains "paperlean-timing native libs=1 modules=2"
{ grep -v "^warning: ignoring native" "$CAPTURED.out.produced" > "$CAPTURED.out.filtered" || true; }
cp "$CAPTURED.out.filtered" "$CAPTURED.out.produced"
expect_output UseN "$TMP_DIR/UseN.expected" "with a damaged manifest"
# A module found first elsewhere in the search path is not read from the pack.
mkdir -p "$TMP_DIR/shadow"
cp "$LIB/N1.olean" "$TMP_DIR/shadow/N1.olean"
capture env LEAN_PATH="$TMP_DIR/shadow:$LIB" "${NATIVE[@]}" lean UseN.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
expect_output UseN "$TMP_DIR/UseN.expected" "with a shadowed module"

# The library's code is used: a manifest written for the library of the first version of N1 after
# the second version is compiled says that the library's code is that of the second version, so the
# import uses the first version's code. (Manifests must be written for the files the library was
# compiled with; this one is not.)
perl -pi -e 's/n \* 2 \+ 1/n * 3 + 1/' N1.lean
compile N1 N2
manifest "$TMP_DIR/libn.paperlean" "$TMP_DIR/libn.so" N1 N2
pack
capture env LEAN_PATH="$LIB" "${NATIVE[@]}" lean UseN.lean
check_out_contains "paperlean-timing native libs=1 modules=2"
check_out_contains "111"
# The module being compiled, which the library also contains, is interpreted, also where the library
# serves what it imports: `N2` is changed (the library's says 100), and its import uses the library
# (`nf 3` is the first version's 7).
mkdir "$TMP_DIR/edited"
printf 'import N1\ndef ng (n : Nat) : Nat := nf n + 200\n#eval ng 3\n' > "$TMP_DIR/edited/N2.lean"
capture env LEAN_PATH="$LIB" "${NATIVE[@]}" lean -R "$TMP_DIR/edited" "$TMP_DIR/edited/N2.lean"
check_out_matches "paperlean-timing native libs=1 .*verified=[1-9]"
{ grep -v "^paperlean-" "$CAPTURED.out.produced" || true; } > "$TMP_DIR/N2.out"
[ "$(cat "$TMP_DIR/N2.out")" = 207 ] || fail "N2 in the library, not the one being compiled, ran: $(cat "$TMP_DIR/N2.out")"

# After a change of N1, the library no longer matches and is not used. (A manifest knows files by
# their contents, which compiling them again with the same source does not change.)
perl -pi -e 's/n \* 3 \+ 1/n * 3 + 2/' N1.lean
compile N1 N2
pack
capture env LEAN_PATH="$LIB" lean UseN.lean
check_out_contains "117"
cp "$CAPTURED.out.produced" "$TMP_DIR/UseN.changed"
capture env LEAN_PATH="$LIB" "${NATIVE[@]}" lean UseN.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
expect_output UseN "$TMP_DIR/UseN.changed" "with a stale native library"

# Module files: all native code of a module imported for compile time (`meta import`), whose runtime
# initializer runs too, is used; only its `meta` code if it is imported for run time only. A changed
# IR file (here that of another version of the module, whose `.olean` file stays) disables the library
# for the module.
cat > MA.lean <<'END'
module
public def ma (n : Nat) : Nat := n + 7
public meta def mm (n : Nat) : Nat := n + 9
END
cat > UseM.lean <<'END'
module
meta import MA
#eval ma 1
END
cat > UseR.lean <<'END'
module
import MA
public def r : Nat := ma 2
#eval mm 1
END
run env LEAN_PATH="$LIB" lean -Dcompiler.postponeCompile=false -o "$LIB/MA.olean" -i "$LIB/MA.ilean" -c "$TMP_DIR/MA.c" MA.lean
link "$TMP_DIR/libm.so" MA
manifest "$TMP_DIR/libm.paperlean" "$TMP_DIR/libm.so" MA
pack
NATIVE_M=(LEAN_OLEAN_PACK="$TMP_DIR/n.paperlean" PAPERLEAN_NATIVE_LIBS="$TMP_DIR/libm.paperlean" PAPERLEAN_IMPORT_TIMING=1)
for f in UseM UseR; do
  capture env LEAN_PATH="$LIB" lean $f.lean
  cp "$CAPTURED.out.produced" "$TMP_DIR/$f.expected"
done
check_out_contains "10"
capture env LEAN_PATH="$LIB" "${NATIVE_M[@]}" lean UseM.lean
check_out_contains "paperlean-timing native libs=1 modules=1 meta=0"
expect_output UseM "$TMP_DIR/UseM.expected" "with the native library"
capture env LEAN_PATH="$LIB" "${NATIVE_M[@]}" lean UseR.lean
check_out_contains "paperlean-timing native libs=1 modules=0 meta=1"
expect_output UseR "$TMP_DIR/UseR.expected" "with the native library"
mkdir "$TMP_DIR/ma2"
sed 's/n + 7/n + 8/' MA.lean > "$TMP_DIR/ma2/MA.lean"
run env LEAN_PATH="$LIB" lean -R "$TMP_DIR/ma2" -Dcompiler.postponeCompile=false -o "$TMP_DIR/ma2/MA.olean" \
  -i "$TMP_DIR/ma2/MA.ilean" "$TMP_DIR/ma2/MA.lean"
cp "$TMP_DIR/ma2/MA.ir" "$LIB/MA.ir"
pack
capture env LEAN_PATH="$LIB" lean UseM.lean
cp "$CAPTURED.out.produced" "$TMP_DIR/UseM.changed"
capture env LEAN_PATH="$LIB" "${NATIVE_M[@]}" lean UseM.lean
check_out_contains "paperlean-timing native libs=0 modules=0 meta=0"
expect_output UseM "$TMP_DIR/UseM.changed" "with a changed IR file"

# `meta` code can use declarations that the compiler generates, which belong to both phases and which
# the runtime initializer initializes (here a boxed character of `dein`): the `meta` code of a module
# imported for run time only, whose runtime initializer does not run, is interpreted then.
cat > MB.lean <<'END'
module
public meta section
def dein (n : Nat) (s : String) : String := s.replace (String.ofList ('\n' :: List.replicate n ' ')) " "
public def mbLen (s : String) : Nat := (dein 2 s).length
end
END
cat > UseB.lean <<'END'
module
import MB
#eval mbLen "a\n  b"
END
run env LEAN_PATH="$LIB" lean -Dcompiler.postponeCompile=false -o "$LIB/MB.olean" -i "$LIB/MB.ilean" -c "$TMP_DIR/MB.c" MB.lean
awk '/^LEAN_EXPORT lean_object\* runtime_initialize_/,/^}/' "$TMP_DIR/MB.c" | grep -q "boxed__const" ||
  fail "MB's runtime initializer initializes no compiler-generated declaration; the test does not test this"
link "$TMP_DIR/libb.so" MB
manifest "$TMP_DIR/libb.paperlean" "$TMP_DIR/libb.so" MB
pack
capture env LEAN_PATH="$LIB" lean UseB.lean
check_out_contains "3"
cp "$CAPTURED.out.produced" "$TMP_DIR/UseB.expected"
capture env LEAN_PATH="$LIB" LEAN_OLEAN_PACK="$TMP_DIR/n.paperlean" PAPERLEAN_NATIVE_LIBS="$TMP_DIR/libb.paperlean" \
  PAPERLEAN_IMPORT_TIMING=1 lean UseB.lean
check_out_contains "paperlean-timing native libs=0 modules=0 meta=0"
expect_output UseB "$TMP_DIR/UseB.expected" "with a runtime initializer that initializes declarations"
# A module whose runtime initializer initializes declarations that its `meta` code does not use (the
# manifest records that from its `.c` file): its `meta` code is used, with the same output.
cat > MC.lean <<'END'
module
public def mcTable : Array Nat := (List.range 5).toArray.map (· * 3)
public meta def mcf (n : Nat) : Nat := n + 9
END
cat > UseC.lean <<'END'
module
import MC
#eval mcf 1
END
run env LEAN_PATH="$LIB" lean -Dcompiler.postponeCompile=false -o "$LIB/MC.olean" -i "$LIB/MC.ilean" -c "$TMP_DIR/MC.c" MC.lean
awk '/^LEAN_EXPORT lean_object\* runtime_initialize_/,/^}/' "$TMP_DIR/MC.c" | grep -q "mcTable = " ||
  fail "MC's runtime initializer initializes no declaration; the test does not test this"
link "$TMP_DIR/libc.so" MC
manifest "$TMP_DIR/libc.paperlean" "$TMP_DIR/libc.so" MC
pack
capture env LEAN_PATH="$LIB" lean UseC.lean
check_out_contains "10"
cp "$CAPTURED.out.produced" "$TMP_DIR/UseC.expected"
capture env LEAN_PATH="$LIB" LEAN_OLEAN_PACK="$TMP_DIR/n.paperlean" PAPERLEAN_NATIVE_LIBS="$TMP_DIR/libc.paperlean" \
  PAPERLEAN_IMPORT_TIMING=1 lean UseC.lean
check_out_contains "paperlean-timing native libs=1 modules=0 meta=1"
expect_output UseC "$TMP_DIR/UseC.expected" "with a runtime initializer that initializes declarations that meta code does not use"

# The compile-time initializer of a module that comes before one of its indirect imports in the
# import order (P2's private import P1 is imported only after P2): whether it may run before the
# compile-time initializers of those that the manifest says what it runs. P2's initializes a
# declaration with P2's own code and Lean's, so P2's native code is used; P3's calls P1's code, which
# may need P1's initializer, so P3 is interpreted. The output is the same.
cat > P1.lean <<'END'
module
public structure P1S where
  x : Nat
  h : x = x := by rfl
@[noinline] public meta def p1f (n : Nat) : Nat := n + 1
END
cat > P2.lean <<'END'
module
import P1
public structure P2S where
  y : Nat
  h : y = y := by rfl
END
cat > P3.lean <<'END'
module
import P1
meta def p3c : Nat := p1f 2
public def p3 : Nat := 3
END
cat > UseP.lean <<'END'
module
import P2
import P3
import P1
def s : P2S := { y := 3 }
#check p3
#eval s.y
END
compile -c P1 P2 P3
link "$TMP_DIR/libp.so" P1 P2 P3
manifest "$TMP_DIR/libp.paperlean" "$TMP_DIR/libp.so" P1 P2 P3
pack
capture env LEAN_PATH="$LIB" lean UseP.lean
check_out_contains "3"
cp "$CAPTURED.out.produced" "$TMP_DIR/UseP.expected"
capture env LEAN_PATH="$LIB" LEAN_OLEAN_PACK="$TMP_DIR/n.paperlean" PAPERLEAN_NATIVE_LIBS="$TMP_DIR/libp.paperlean" \
  PAPERLEAN_IMPORT_TIMING=1 lean UseP.lean
check_out_contains "paperlean-timing native libs=1 modules=0 meta=2 verified=3 importsNotUsed=0 initOrder=1"
expect_output UseP "$TMP_DIR/UseP.expected" "with compile-time initializers before those of indirect imports"

# Native functions that the interpreter calls through their boxed versions (scalar parameters or
# results), which it looks up only for declarations whose IR has one, and through their unboxed
# versions, from a module whose native code is used and from one whose code is not (G2's library
# is of another version of G2).
cat > G1.lean <<'END'
@[noinline] def gScale (x : UInt64) (b : Bool) : UInt64 := if b then x * 2 else x + 1
@[noinline] def gList (n : Nat) : List Nat := List.range n
@[noinline] def gFloat (x : Float) : Float := x * 1.5
END
cat > G2.lean <<'END'
import G1
@[noinline] def gBoth (x : UInt64) : UInt64 := gScale x true + gScale x false
END
cat > UseG.lean <<'END'
import G2
#eval gScale 21 true
#eval gBoth 5
#eval gList 4
#eval gFloat 2.0
#eval (List.range 50).foldl (fun a n => a + gScale n.toUInt64 (n % 2 == 0)) 0
END
compile -c G1 G2
link "$TMP_DIR/libg.so" G1 G2
manifest "$TMP_DIR/libg.paperlean" "$TMP_DIR/libg.so" G1 G2
perl -pi -e 's/gScale x false/gScale x false + 1/' G2.lean
compile G2
pack
capture env LEAN_PATH="$LIB" lean UseG.lean
check_out_contains "42"
cp "$CAPTURED.out.produced" "$TMP_DIR/UseG.expected"
capture env LEAN_PATH="$LIB" LEAN_OLEAN_PACK="$TMP_DIR/n.paperlean" PAPERLEAN_NATIVE_LIBS="$TMP_DIR/libg.paperlean" \
  PAPERLEAN_IMPORT_TIMING=1 lean UseG.lean
check_out_contains "paperlean-timing native libs=1 modules=1"
expect_output UseG "$TMP_DIR/UseG.expected" "calling native functions through their boxed versions"

# A module imported for run time only whose private import is not imported at all: its native code is
# used if its compile-time initializer runs only its own code and Lean's (Q2's), not otherwise (Q3's
# calls Q1's code).
cat > Q1.lean <<'END'
module
@[noinline] public meta def q1f (n : Nat) : Nat := n + 1
public def q1 : Nat := 1
END
cat > Q2.lean <<'END'
module
import Q1
public structure Q2S where
  y : Nat
  h : y = y := by rfl
public meta def q2f (n : Nat) : Nat := n + 2
END
cat > Q3.lean <<'END'
module
import Q1
meta def q3c : Nat := q1f 2
public meta def q3f (n : Nat) : Nat := n + 3
END
cat > UseQ.lean <<'END'
module
import Q2
import Q3
def s : Q2S := { y := 3 }
#eval q2f s.y
#eval q3f 1
END
compile -c Q1 Q2 Q3
link "$TMP_DIR/libq.so" Q1 Q2 Q3
manifest "$TMP_DIR/libq.paperlean" "$TMP_DIR/libq.so" Q1 Q2 Q3
pack
capture env LEAN_PATH="$LIB" lean UseQ.lean
check_out_contains "5"
cp "$CAPTURED.out.produced" "$TMP_DIR/UseQ.expected"
capture env LEAN_PATH="$LIB" LEAN_OLEAN_PACK="$TMP_DIR/n.paperlean" PAPERLEAN_NATIVE_LIBS="$TMP_DIR/libq.paperlean" \
  PAPERLEAN_IMPORT_TIMING=1 lean UseQ.lean
check_out_contains "paperlean-timing native libs=1 modules=0 meta=1 verified=2 importsNotUsed=1"
expect_output UseQ "$TMP_DIR/UseQ.expected" "with a private import that is not imported"

# `meta` declarations with `@[export]` names, public and private: the manifest records their export
# names (copies of the module data's strings, which the regions free), and their code is used.
cat > XE.lean <<'END'
module
@[export lean_paperlean_test_xe_pub] public meta def xePub (n : Nat) : Nat := n * 10
@[export lean_paperlean_test_xe_priv] meta def xePriv (n : Nat) : Nat := n * 100
public meta def xeBoth (n : Nat) : Nat := xePub n + xePriv n
END
cat > UseXE.lean <<'END'
module
import XE
#eval xeBoth 2
#eval xePub 3
END
run env LEAN_PATH="$LIB" lean -Dcompiler.postponeCompile=false -o "$LIB/XE.olean" -i "$LIB/XE.ilean" -c "$TMP_DIR/XE.c" XE.lean
link "$TMP_DIR/libxe.so" XE
manifest "$TMP_DIR/libxe.paperlean" "$TMP_DIR/libxe.so" XE
pack
capture env LEAN_PATH="$LIB" lean UseXE.lean
check_out_contains "220"
cp "$CAPTURED.out.produced" "$TMP_DIR/UseXE.expected"
capture env LEAN_PATH="$LIB" LEAN_OLEAN_PACK="$TMP_DIR/n.paperlean" PAPERLEAN_NATIVE_LIBS="$TMP_DIR/libxe.paperlean" \
  PAPERLEAN_IMPORT_TIMING=1 lean UseXE.lean
check_out_contains "paperlean-timing native libs=1 modules=0 meta=1"
expect_output UseXE "$TMP_DIR/UseXE.expected" "with exported meta declarations"
