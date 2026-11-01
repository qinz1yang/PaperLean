# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that native libraries of packages (`src/paperlean/native_libs.cpp`, `verify`) run nothing that
# Lean's interpreter would not: a module that declares `@[extern]` functions (the interpreter calls
# none of a package's) or has `builtin_initialize` declarations (only native initializers run them)
# is interpreted, with the modules that import it, also if an import has only its IR; a module whose
# native code was initialized keeps that code when the process imports the same module again, and
# none of its initializers runs again, whichever phase a later import asks for; a module with other
# files is interpreted then; a module whose native initializers would run its `[init]` declarations
# in another order than Lean's interpreter is interpreted.

cp native_helper.lean "$TMP_DIR/"
SRC="$TMP_DIR/src"
LIB="$TMP_DIR/lib"
mkdir -p "$SRC" "$LIB"
cd "$SRC"

cat > "$TMP_DIR/pack.lean" <<'END'
import Lean.PaperLean.OLeanPack
def main (args : List String) : IO Unit := do
  let n ← Lean.PaperLean.OLeanPack.create #[args[1]!] args[0]!
  IO.println s!"packed: {decide (n > 0)}"
END
# Compiles modules to `.olean` and `.c` files, links them into <library>, writes its manifest, and
# packs all of them: build <name> <module>...
build() {
  local name=$1; shift
  local cs=()
  for m in "$@"; do
    run env LEAN_PATH="$LIB" lean -o "$LIB/$m.olean" -i "$LIB/$m.ilean" -c "$TMP_DIR/$m.c" $m.lean
    cs+=("$TMP_DIR/$m.c")
  done
  run leanc -shared -DLEAN_EXPORTING -o "$TMP_DIR/$name.so" "${cs[@]}"
  capture env LEAN_PATH="$LIB" lean --run "$TMP_DIR/native_helper.lean" manifest "$TMP_DIR/$name.paperlean" "$TMP_DIR/$name.so" "$TMP_DIR" "$@"
  check_out_contains "manifest written"
  capture lean --run "$TMP_DIR/pack.lean" "$TMP_DIR/n.paperlean" "$LIB"
  check_out_contains "packed: true"
}
# Whether the output of the last command, without the timing lines, is that in <file>:
# same_output <file> <what>
same_output() {
  { grep -v "^paperlean-" "$CAPTURED.out.produced" || true; } | $DIFF -- "$1" - || fail "the output differs: $2"
}
# Runs <file> with the native libraries <name>..., expecting exit code <code>:
# native <code> <file> <name>...
native() {
  local code=$1 f=$2; shift 2
  local libs=()
  for n in "$@"; do libs+=("$TMP_DIR/$n.paperlean"); done
  capture_exit "$code" env LEAN_PATH="$LIB" LEAN_OLEAN_PACK="$TMP_DIR/n.paperlean" \
    PAPERLEAN_NATIVE_LIBS="$(IFS=:; echo "${libs[*]}")" PAPERLEAN_IMPORT_TIMING=1 lean "$f"
}

# A package's `@[extern]` function: Lean's interpreter finds no implementation, also when another
# module exports a function under its symbol, and `native_decide` fails.
cat > XB.lean <<'END'
@[extern "lean_paperlean_test_myfn"] opaque myFn : Nat → Nat
END
cat > XA.lean <<'END'
import XB
@[export lean_paperlean_test_myfn] def myImpl (n : Nat) : Nat := n + 1000
END
cat > XN.lean <<'END'
import XB
@[noinline] def useIt (n : Nat) : Nat := myFn n + 1
END
cat > UseX.lean <<'END'
import XA
import XN
theorem t : useIt 1 = 1002 := by native_decide
END
build libx XB XA XN
capture_exit 1 env LEAN_PATH="$LIB" lean UseX.lean
check_out_contains "Could not find native implementation of external declaration 'myFn'"
native 1 UseX.lean libx
check_out_contains "Could not find native implementation of external declaration 'myFn'"
check_out_contains "paperlean-timing native libs=0 modules=0"

# A package's `builtin_initialize`: importing the module runs it only natively, so it is interpreted
# and the attribute it would register is unknown, as in Lean.
cat > BA.lean <<'END'
import Lean
open Lean
builtin_initialize registerBuiltinAttribute {
  name := `myattr, descr := "registered by `builtin_initialize`", add := fun _ _ _ => pure () }
END
cat > BB.lean <<'END'
import BA
def bb : Nat := 2
END
cat > UseBA.lean <<'END'
import BB
@[myattr] def foo : Nat := 1
END
build liba BA BB
capture_exit 1 env LEAN_PATH="$LIB" lean UseBA.lean
check_out_contains "Unknown attribute"
native 1 UseBA.lean liba
check_out_contains "Unknown attribute"

# A second import of a module in the same process, after its initializers ran natively: they do not
# run again (registering the extension twice would fail).
cat > E1.lean <<'END'
import Lean
open Lean
initialize myExt : SimplePersistentEnvExtension Nat (List Nat) ←
  registerSimplePersistentEnvExtension { addEntryFn := fun l n => n :: l, addImportedFn := fun _ => [] }
def ef (n : Nat) : Nat := n + 1
END
cat > UseE.lean <<'END'
import Lean
import E1
open Lean in
#eval show IO Unit from do
  (unsafe enableInitializersExecution : IO Unit)
  let env ← importModules #[{ module := `E1 }] {} (loadExts := true)
  IO.println s!"imported again: {env.contains `ef}"
#eval ef 1
END
build libe E1
capture_exit 0 env LEAN_PATH="$LIB" lean UseE.lean
check_out_contains "imported again: true"
native 0 UseE.lean libe
check_out_contains "paperlean-timing native libs=1 modules=1"
check_out_contains "imported again: true"

# A module whose code Lean loaded otherwise (`--load-dynlib`) while a library has it too: the
# library's code for the module's importers would use the library's copy of the module's state, so
# it is not used, and the state is one, as in Lean.
cat > C1.lean <<'END'
initialize counter : IO.Ref Nat ← IO.mkRef 0
def bump : IO Nat := do counter.modify (· + 1); counter.get
END
cat > C2.lean <<'END'
import C1
@[noinline] def bump2 : IO Nat := bump
END
cat > UseC.lean <<'END'
import C2
#eval bump
#eval bump2
#eval bump
END
build libc C1 C2
run leanc -shared -DLEAN_EXPORTING -o "$TMP_DIR/libpre.so" "$TMP_DIR/C1.c"
capture_exit 0 env LEAN_PATH="$LIB" lean --load-dynlib="$TMP_DIR/libpre.so" UseC.lean
printf '1\n2\n3\n' | $DIFF -- - "$CAPTURED.out.produced" || fail "UseC.lean differs from what Lean prints"
capture_exit 0 env LEAN_PATH="$LIB" LEAN_OLEAN_PACK="$TMP_DIR/n.paperlean" \
  PAPERLEAN_NATIVE_LIBS="$TMP_DIR/libc.paperlean" lean --load-dynlib="$TMP_DIR/libpre.so" UseC.lean
printf '1\n2\n3\n' | $DIFF -- - "$CAPTURED.out.produced" || fail "a module loaded twice has two states"

# The same with C1 compiled into the main program, which Lean's own code is: C2 is interpreted too.
cat > MainC.lean <<'END'
import Lean
import C1
def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  unsafe Lean.enableInitializersExecution
  let env? ← Lean.Elab.runFrontend (← IO.FS.readFile args[0]!) {} args[0]! `UseC
  return if env?.isSome then 0 else 1
END
run env LEAN_PATH="$LIB" lean -c "$TMP_DIR/MainC.c" MainC.lean
LEAN_LIBDIR="$(lean --print-libdir)"
if [[ "$(uname)" == Darwin ]]; then
  shared=("$LEAN_LIBDIR"/libInit_shared.dylib "$LEAN_LIBDIR"/libleanshared*.dylib); exports=-Wl,-export_dynamic
else
  shared=("$LEAN_LIBDIR"/libInit_shared.so "$LEAN_LIBDIR"/libleanshared*.so); exports=-rdynamic
fi
run leanc -DLEAN_EXPORTING -o "$TMP_DIR/mainc" "$TMP_DIR/MainC.c" "$TMP_DIR/C1.c" "${shared[@]}" \
  "-Wl,-rpath,$LEAN_LIBDIR" $exports
capture_exit 0 env LEAN_PATH="$LIB" "$TMP_DIR/mainc" UseC.lean
printf '1\n2\n3\n' | $DIFF -- - "$CAPTURED.out.produced" || fail "UseC.lean differs from what Lean prints"
capture_exit 0 env LEAN_PATH="$LIB" LEAN_OLEAN_PACK="$TMP_DIR/n.paperlean" \
  PAPERLEAN_NATIVE_LIBS="$TMP_DIR/libc.paperlean" "$TMP_DIR/mainc" UseC.lean
printf '1\n2\n3\n' | $DIFF -- - "$CAPTURED.out.produced" || fail "a module compiled into the program has two states"

# The same with the `@[extern]` function in a module whose import has only the IR (it is reached
# through a private import of a module imported with `meta import`): the data that the manifest
# recorded tell that the module declares it.
cat > RC.lean <<'END'
module
@[extern "lean_paperlean_test_rcfn"] opaque rcfn : Nat → Nat
@[export lean_paperlean_test_rcfn] def rcimpl (n : Nat) : Nat := n + 1000
public def useRc (n : Nat) : Nat := rcfn n + 1
END
cat > RB.lean <<'END'
module
import RC
public def rbf (n : Nat) : Nat := useRc n
END
cat > UseRB.lean <<'END'
module
meta import RB
theorem t : rbf 1 = 1002 := by native_decide
END
build libr RC RB
capture_exit 1 env LEAN_PATH="$LIB" lean UseRB.lean
check_out_contains "Could not find native implementation of external declaration '_private.RC.0.rcfn'"
native 1 UseRB.lean libr
check_out_contains "Could not find native implementation of external declaration '_private.RC.0.rcfn'"
# ... and with a `builtin_initialize` declaration there.
cat > RD.lean <<'END'
module
public import Lean
open Lean
builtin_initialize registerBuiltinAttribute {
  name := `rdattr, descr := "registered by `builtin_initialize`", add := fun _ _ _ => pure () }
public def rdf (n : Nat) : Nat := n + 1
END
cat > RE.lean <<'END'
module
import RD
public def ref1 (n : Nat) : Nat := rdf n
END
cat > UseRE.lean <<'END'
module
meta import RE
@[rdattr] def foo : Nat := 1
END
build libd RD RE
capture_exit 1 env LEAN_PATH="$LIB" lean UseRE.lean
check_out_contains "Unknown attribute"
native 1 UseRE.lean libd
check_out_contains "Unknown attribute"

# A second import of a module of the same name with other files, after the native initializers of
# the first one ran: its code is interpreted, with the `[init]` values of the first one, as Lean
# keeps them.
cat > S1.lean <<'END'
initialize sRef : IO.Ref Nat ← IO.mkRef 7
@[noinline] def sf (n : Nat) : Nat := n + 1
END
mkdir -p "$TMP_DIR/src2" "$TMP_DIR/lib2"
sed 's/n + 1/n + 2/' S1.lean > "$TMP_DIR/src2/S1.lean"
(cd "$TMP_DIR/src2" && run lean -o "$TMP_DIR/lib2/S1.olean" S1.lean)
cat > UseS.lean <<END
import Lean
import S1
open Lean in
#eval show IO Unit from do
  (unsafe enableInitializersExecution : IO Unit)
  initSearchPath (← findSysroot) [⟨"$TMP_DIR/lib2"⟩]
  let env ← importModules #[{ module := \`S1 }] {} (loadExts := true)
  let f ← IO.ofExcept <| unsafe env.evalConst (Nat → Nat) {} \`sf
  let r ← IO.ofExcept <| unsafe env.evalConst (IO.Ref Nat) {} \`sRef
  r.modify (· + 1)
  IO.println s!"second import: sf 1 = {f 1}, sRef = {← r.get}"
#eval sf 1
#eval show IO Nat from sRef.get
END
build libs S1
capture_exit 0 env LEAN_PATH="$LIB" lean UseS.lean
check_out_contains "second import: sf 1 = 3, sRef = 8"
cp "$CAPTURED.out.produced" "$TMP_DIR/UseS.expected"
native 0 UseS.lean libs
check_out_contains "paperlean-timing native libs=1 modules=1"
same_output "$TMP_DIR/UseS.expected" "a second import of other files of a module"

# A later import of a module whose native initializers ran asks for those of another phase (that of
# a `module` after an import that is not one, and the other way round): they do not run again.
cat > T1.lean <<'END'
module
initialize IO.println "the initializer of T1 ran"
public def tf (n : Nat) : Nat := n + 1
END
cat > UseT.lean <<'END'
import Lean
import T1
open Lean in
#eval show IO Unit from do
  (unsafe enableInitializersExecution : IO Unit)
  let env ← importModules #[{ module := `T1 }] {} (loadExts := true) (level := .exported)
  IO.println s!"imported as a module: {env.contains `tf}"
END
cat > UseT2.lean <<'END'
module
meta import Lean
import Lean.ImportingFlag
meta import T1
open Lean in
#eval show IO Unit from do
  (unsafe enableInitializersExecution : IO Unit)
  let env ← importModules #[{ module := `T1 }] {} (loadExts := true)
  IO.println s!"imported, not as a module: {env.contains `tf}"
END
build libt T1
for f in UseT UseT2; do
  capture_exit 0 env LEAN_PATH="$LIB" lean $f.lean
  cp "$CAPTURED.out.produced" "$TMP_DIR/$f.expected"
  [[ $(grep -c "the initializer of T1 ran" "$TMP_DIR/$f.expected") == 1 ]] || fail "$f: T1's initializer did not run once in Lean"
  native 0 $f.lean libt
  check_out_contains "paperlean-timing native libs=1 modules=1"
  same_output "$TMP_DIR/$f.expected" "$f: a later import asking for another phase's initializer"
done

# A module with `[init]` declarations of both phases: its native initializers would run them in
# another order than Lean's interpreter, so it is interpreted.
cat > U1.lean <<'END'
module
meta initialize IO.println "compile-time initialization of U1"
initialize IO.println "run-time initialization of U1"
public def uf (n : Nat) : Nat := n + 1
END
cat > UseU.lean <<'END'
import U1
#eval uf 1
END
cat > UseU2.lean <<'END'
module
meta import U1
#eval uf 1
END
build libu U1
for f in UseU UseU2; do
  capture_exit 0 env LEAN_PATH="$LIB" lean $f.lean
  cp "$CAPTURED.out.produced" "$TMP_DIR/$f.expected"
  native 0 $f.lean libu
  same_output "$TMP_DIR/$f.expected" "$f: initializers of both phases"
done

# Modules of a package (`--setup`), whose symbols have its prefix: a module whose native code is not
# used is interpreted without looking up its symbols, unless Lean loaded a shared library, which may
# have them (here `--load-dynlib` of another module of the package with a declaration of the same
# name, whose code Lean then calls, as it calls any code that it finds first).
cat > PNew.lean <<'END'
@[extern "lean_paperlean_test_pnew"] opaque pNewExt : Nat → Nat
def Shared.helper (n : Nat) : Nat := n + 1
def pNewOther (n : Nat) : Nat := Shared.helper n * 2
END
cat > POld.lean <<'END'
def Shared.helper (n : Nat) : Nat := n + 1000
END
cat > PUse.lean <<'END'
import PNew
#eval Shared.helper 5
#eval pNewOther 5
END
cat > PUse2.lean <<'END'
import PNew
#eval Shared.helper 5
END
for m in PNew POld; do
  printf '{"name":"%s","package":"pkg","isModule":false,"dynlibs":[],"importArts":{},"options":{},"plugins":[]}' $m > "$TMP_DIR/$m.setup.json"
  run env LEAN_PATH="$LIB" lean --setup "$TMP_DIR/$m.setup.json" -o "$LIB/$m.olean" -i "$LIB/$m.ilean" -c "$TMP_DIR/$m.c" $m.lean
done
grep -q "lp_pkg_Shared_helper" "$TMP_DIR/PNew.c" || fail "PNew's symbols do not have the package's prefix"
printf '#include <lean/lean.h>\nLEAN_EXPORT lean_object* lean_paperlean_test_pnew(lean_object* x) { return x; }\n' > "$TMP_DIR/pnewext.c"
run leanc -shared -DLEAN_EXPORTING -o "$TMP_DIR/libpnew.so" "$TMP_DIR/PNew.c" "$TMP_DIR/pnewext.c"
run leanc -shared -DLEAN_EXPORTING -o "$TMP_DIR/libpold.so" "$TMP_DIR/POld.c"
capture env LEAN_PATH="$LIB" lean --run "$TMP_DIR/native_helper.lean" manifest "$TMP_DIR/libpnew.paperlean" "$TMP_DIR/libpnew.so" "$TMP_DIR" PNew
check_out_contains "manifest written"
capture lean --run "$TMP_DIR/pack.lean" "$TMP_DIR/n.paperlean" "$LIB"
capture_exit 0 env LEAN_PATH="$LIB" lean PUse.lean
printf '6\n12\n' | $DIFF -- - "$CAPTURED.out.produced" || fail "PUse.lean differs from what Lean prints"
native 0 PUse.lean libpnew
check_out_contains "paperlean-timing native libs=0 modules=0 meta=0 verified=1"
{ grep -v "^paperlean-" "$CAPTURED.out.produced" || true; } | $DIFF -- <(printf '6\n12\n') - ||
  fail "a package's module whose native code is not used"
capture_exit 0 env LEAN_PATH="$LIB" lean --load-dynlib="$TMP_DIR/libpold.so" PUse2.lean
cp "$CAPTURED.out.produced" "$TMP_DIR/PUse2.expected"
capture_exit 0 env LEAN_PATH="$LIB" LEAN_OLEAN_PACK="$TMP_DIR/n.paperlean" PAPERLEAN_NATIVE_LIBS="$TMP_DIR/libpnew.paperlean" \
  lean --load-dynlib="$TMP_DIR/libpold.so" PUse2.lean
$DIFF -- "$TMP_DIR/PUse2.expected" "$CAPTURED.out.produced" || fail "with a library loaded by --load-dynlib"
