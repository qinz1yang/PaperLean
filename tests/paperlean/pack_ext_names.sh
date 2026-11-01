# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that olean packs and import images keep extensions apart whose names differ only in how
# their characters are divided into components: `x.y` and the one component "x\0sy" have the same
# characters and markers in a naive key.

SRC="$TMP_DIR/src"
LIB="$TMP_DIR/lib"
mkdir -p "$SRC/R" "$LIB/R"
cd "$SRC"
cat > R/Ext.lean <<'END'
import Lean
open Lean
initialize extA : SimplePersistentEnvExtension Nat (List Nat) ←
  registerSimplePersistentEnvExtension {
    name := Name.mkStr .anonymous "x\x00sy"
    addEntryFn := fun s n => n :: s
    addImportedFn := fun as => as.foldl (fun s a => a.toList ++ s) [] }
initialize extB : SimplePersistentEnvExtension Nat (List Nat) ←
  registerSimplePersistentEnvExtension {
    name := `x.y
    addEntryFn := fun s n => n :: s
    addImportedFn := fun as => as.foldl (fun s a => a.toList ++ s) [] }
END
cat > R/M.lean <<'END'
import R.Ext
open Lean
run_cmd modifyEnv fun env => extA.addEntry env 1
run_cmd modifyEnv fun env => extB.addEntry env 2
END
cat > Test.lean <<'END'
import R.M
open Lean
#eval show CoreM Unit from do
  IO.println s!"extA: {extA.getState (← getEnv)}, extB: {extB.getState (← getEnv)}"
END
run env LEAN_PATH="$LIB" lean -o "$LIB/R/Ext.olean" R/Ext.lean
run env LEAN_PATH="$LIB" lean -o "$LIB/R/M.olean" R/M.lean
cat > "$TMP_DIR/pack.lean" <<'END'
import Lean.PaperLean.OLeanPack
def main (args : List String) : IO Unit := do
  let n ← Lean.PaperLean.OLeanPack.create #[args[1]!] args[0]!
  IO.println s!"packed: {decide (n > 0)}"
END
capture lean --run "$TMP_DIR/pack.lean" "$TMP_DIR/r.paperlean" "$LIB"
check_out_contains "packed: true"
capture env LEAN_PATH="$LIB" lean Test.lean
check_out_contains "extA: [1], extB: [2]"
capture env LEAN_PATH="$LIB" LEAN_OLEAN_PACK="$TMP_DIR/r.paperlean" lean Test.lean
check_out_contains "extA: [1], extB: [2]"
