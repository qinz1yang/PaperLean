# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that a process that imports again checks olean packs again: an `.olean` file replaced between
# two imports, or a root directory of a pack replaced after the pack was loaded, is read from disk
# as without packs, on every import path.

SRC="$TMP_DIR/src"
mkdir -p "$SRC" "$TMP_DIR/root" "$TMP_DIR/v2"
cd "$SRC"
echo 'def a : Nat := 1' > A1.lean
printf 'def a : Nat := 2\ndef onlyInV2 : Nat := 3\n' > A2.lean
cat > "$TMP_DIR/pack.lean" <<'END'
import Lean.PaperLean.OLeanPack
def main (args : List String) : IO Unit := do
  let n ← Lean.PaperLean.OLeanPack.create #[args[1]!] args[0]!
  IO.println s!"packed: {decide (n > 0)}"
END
cat > Again.lean <<'END'
import Lean
open Lean
def val (env : Environment) : String :=
  match env.find? `a with
  | some (.defnInfo d) => s!"a = {d.value}, onlyInV2: {env.contains `onlyInV2}"
  | _ => "none"
def main (args : List String) : IO Unit := do
  let [root, v2] := args | throw <| IO.userError "usage"
  initSearchPath (← findSysroot)
  IO.println s!"first: {val (← importModules #[{module := `A}] {})}"
  IO.FS.writeBinFile (root ++ "/A.olean.new") (← IO.FS.readBinFile v2)
  IO.FS.rename (root ++ "/A.olean.new") (root ++ "/A.olean")
  IO.println s!"second: {val (← importModules #[{module := `A}] {})}"
END
cat > Dir.lean <<'END'
import Lean
open Lean
def val (env : Environment) : String :=
  match env.find? `a with
  | some (.defnInfo d) => s!"a = {d.value}, onlyInV2: {env.contains `onlyInV2}"
  | _ => "none"
-- the root is replaced after an import opened it
def main (args : List String) : IO Unit := do
  let [root, v2] := args | throw <| IO.userError "usage"
  initSearchPath (← findSysroot)
  IO.println s!"first: {val (← importModules #[{module := `A}] {})}"
  IO.FS.rename root (root ++ ".old")
  IO.FS.createDirAll root
  IO.FS.writeBinFile (root ++ "/A.olean") (← IO.FS.readBinFile v2)
  IO.println s!"second: {val (← importModules #[{module := `A}] {})}"
END

setup() {
  rm -rf "$TMP_DIR/root" "$TMP_DIR/root.old"
  mkdir -p "$TMP_DIR/root"
  run lean -o "$TMP_DIR/root/A.olean" A1.lean
  run lean -o "$TMP_DIR/v2/A.olean" A2.lean
  capture lean --run "$TMP_DIR/pack.lean" "$TMP_DIR/a.paperlean" "$TMP_DIR/root"
  check_out_contains "packed: true"
}
for mode in fast legacy check; do
  for prog in Again Dir; do
    setup
    capture env LEAN_PATH="$TMP_DIR/root" LEAN_OLEAN_PACK="$TMP_DIR/a.paperlean" \
      $( [ $mode = legacy ] && echo PAPERLEAN_IMPORT=legacy; [ $mode = check ] && echo PAPERLEAN_IMPORT=check ) \
      lean --run $prog.lean "$TMP_DIR/root" "$TMP_DIR/v2/A.olean"
    check_out_contains "first: a = OfNat.ofNat.{0} Nat 1 (instOfNatNat 1), onlyInV2: false"
    check_out_contains "second: a = OfNat.ofNat.{0} Nat 2 (instOfNatNat 2), onlyInV2: true"
  done
done
