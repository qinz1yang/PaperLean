# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# A `module` `M` with a non-`meta` `initialize` is imported with its native library, so its native
# initializer stores the value; a changed `M` (same module name, other files) is then imported again in
# the same process and its new code, interpreted, reads the declaration. A plain import keeps the value
# in `g_init_globals`; with the native library the interpreter must keep the value the native
# initializer stored. The declaration's `[init]` attribute of a non-`meta` `initialize` is only in the
# module's `.ir` entries (`registerInitAttrUnsafe.filterExport`), so `filter_native_symbol` must look
# there (`importedHasInit`); before, it saw no `[init]` and the interpreter ran the declaration's dummy
# IR (`Unreachable`: an assertion abort). Checked for a `public` and a private `initialize`.
# (Reported by the rev-native review, finding native-2.)

cd "$TEST_DIR/paperlean"
cp native_helper.lean "$TMP_DIR/"
cat > "$TMP_DIR/pack.lean" <<'END'
import Lean.PaperLean.OLeanPack
def main (args : List String) : IO Unit := do
  let n ← Lean.PaperLean.OLeanPack.create #[args[1]!] args[0]!
  IO.println s!"packed: {decide (n > 0)}"
END

for vis in public private; do
  D="$TMP_DIR/$vis"
  mkdir -p "$D/lib" "$D/lib2" "$D/src" "$D/src2"
  if [ $vis = public ]; then decl="public initialize"; else decl="initialize"; fi
  cat > "$D/src/M.lean" <<END
module
$decl mref : IO.Ref Nat ← IO.mkRef 7
public def getM : IO Nat := mref.get
END
  cat > "$D/src2/M.lean" <<END
module
$decl mref : IO.Ref Nat ← IO.mkRef 7
public def getM : IO Nat := do
  let n ← mref.get
  return n + 100
END
  cat > "$D/src/UseM.lean" <<END
module
import Lean
import Lean.ImportingFlag
meta import M
#eval getM
open Lean in
#eval show IO Unit from do
  (unsafe enableInitializersExecution : IO Unit)
  initSearchPath (← findSysroot) [⟨"$D/lib2"⟩]
  let env ← importModules #[{ module := \`M, isMeta := true }] {} (loadExts := true) (level := .exported)
  let f ← IO.ofExcept <| unsafe env.evalConst (IO Nat) {} \`getM
  IO.println s!"second getM: {← f}"
END
  (cd "$D/src" && run lean -Dcompiler.postponeCompile=false -o "$D/lib/M.olean" -i "$D/lib/M.ilean" -c "$D/M.c" M.lean)
  run leanc -shared -DLEAN_EXPORTING -o "$D/libm.so" "$D/M.c"
  (cd "$D" && run env LEAN_PATH="$D/lib" lean --run "$TMP_DIR/native_helper.lean" manifest libm.paperlean libm.so "$D" M)
  (cd "$D" && run lean --run "$TMP_DIR/pack.lean" "$D/n.paperlean" "$D/lib")
  (cd "$D/src2" && run lean -Dcompiler.postponeCompile=false -o "$D/lib2/M.olean" -i "$D/lib2/M.ilean" -c "$D/M2.c" M.lean)
  cd "$D/src"
  capture env LEAN_PATH="$D/lib" lean UseM.lean
  check_out_contains "second getM: 107"
  capture env LEAN_PATH="$D/lib" LEAN_OLEAN_PACK="$D/n.paperlean" PAPERLEAN_NATIVE_LIBS="$D/libm.paperlean" \
    PAPERLEAN_IMPORT_TIMING=1 lean UseM.lean
  check_out_contains "paperlean-timing native libs=1 modules=1"
  check_out_contains "second getM: 107"
  cd "$TEST_DIR/paperlean"
done
true
