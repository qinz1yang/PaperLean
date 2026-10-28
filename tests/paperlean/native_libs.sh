# Tests native libraries of packages (`PAPERLEAN_NATIVE_LIBS`, `src/paperlean/native_libs.cpp`): an
# import uses a library's native code only for imported modules served from an olean pack whose
# files are those of the library's manifest, and the output is that of interpreting them; the module
# being compiled is interpreted; changed, shadowed or damaged inputs disable the library.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK PAPERLEAN_NATIVE_LIBS
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
# manifest.lean <manifest> <library> <directory of the `.c` files> <module>...
cat > "$TMP_DIR/manifest.lean" <<'END'
import Lean.PaperLean.NativeLibs
def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let mods := (args.drop 3).map fun m => (m.toName, s!"{args[2]!}/{m}.c")
  Lean.PaperLean.writeNativeManifest args[0]! args[1]! #[] mods.toArray
  IO.println "manifest written"
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
  capture env LEAN_PATH="$LIB" lean --run "$TMP_DIR/manifest.lean" "$1" "$2" "$TMP_DIR" "${@:3}"
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
# `PAPERLEAN_HEARTBEATS=lean` turns native code off, so that heartbeats are counted as by Lean.
capture env LEAN_PATH="$LIB" "${NATIVE[@]}" PAPERLEAN_HEARTBEATS=lean lean UseN.lean
if grep -q "native libs=" "$CAPTURED.out.produced"; then fail "native code is used with PAPERLEAN_HEARTBEATS=lean"; fi
expect_output UseN "$TMP_DIR/UseN.expected" "with PAPERLEAN_HEARTBEATS=lean"
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
# The module being compiled, which the library also contains, is interpreted.
capture env LEAN_PATH="$LIB" lean N1.lean
cp "$CAPTURED.out.produced" "$TMP_DIR/N1.expected"
check_out_contains "10"
capture env LEAN_PATH="$LIB" "${NATIVE[@]}" lean N1.lean
expect_output N1 "$TMP_DIR/N1.expected" "with the library of another version"

# After a change of N1, the library no longer matches and is not used.
compile N1 N2
pack
capture env LEAN_PATH="$LIB" lean UseN.lean
check_out_contains "116"
cp "$CAPTURED.out.produced" "$TMP_DIR/UseN.changed"
capture env LEAN_PATH="$LIB" "${NATIVE[@]}" lean UseN.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
expect_output UseN "$TMP_DIR/UseN.changed" "with a stale native library"

# Module files: all native code of a module imported for compile time (`meta import`), whose runtime
# initializer runs too, is used; only its `meta` code if it is imported for run time only. A changed
# IR file disables the library for the module.
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
touch "$LIB/MA.ir"
pack
capture env LEAN_PATH="$LIB" "${NATIVE_M[@]}" lean UseM.lean
check_out_contains "paperlean-timing native libs=0 modules=0 meta=0"
expect_output UseM "$TMP_DIR/UseM.expected" "with a changed IR file"

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
