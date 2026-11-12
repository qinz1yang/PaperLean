# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that a repeated pack lookup is answered from the process's lookup cache only while the
# answer still holds: a diamond of packed imports looks up the same names and module data many
# times, and an `.olean` replaced between two imports of the same process is still read from disk
# on the second import. Both the fast import and `PAPERLEAN_IMPORT=check` must produce Lean's
# output.
case "$(uname -s)" in Linux|Darwin) ;; *) return 0 ;; esac
SRC="$TMP_DIR/src"
LIB="$TMP_DIR/lib"
mkdir -p "$SRC" "$LIB"
cd "$SRC"
cat > A.lean <<'END'
def a : Nat := 1
END
cat > B.lean <<'END'
import A
def b : Nat := a + 1
END
cat > C.lean <<'END'
import A
def c : Nat := a + 2
END
cat > D.lean <<'END'
import B
import C
def d : Nat := b + c
END
for m in A B C D; do
  run env LEAN_PATH="$LIB" lean -o "$LIB/$m.olean" "$m.lean"
done
cat > "$TMP_DIR/pack.lean" <<'END'
import Lean.PaperLean.OLeanPack
def main (args : List String) : IO Unit := do
  let n ← Lean.PaperLean.OLeanPack.create #[args[1]!] args[0]!
  IO.println s!"packed: {n}"
END
capture lean --run "$TMP_DIR/pack.lean" "$TMP_DIR/cache.paperlean" "$LIB"
check_out_contains "packed: 4"
cat > Use.lean <<'END'
import D
#eval d
#eval a
END
for mode in fast check; do
  setting=""
  [ "$mode" = check ] && setting=check
  capture env LEAN_PATH="$LIB" LEAN_OLEAN_PACK="$TMP_DIR/cache.paperlean" \
    PAPERLEAN_IMPORT="$setting" PAPERLEAN_IMPORT_TIMING=1 lean Use.lean
  check_out_contains "paperlean-timing modules.fast packed=4 "
  check_out_contains "6"
done
cat > Again.lean <<'END'
import Lean
open Lean
def val (env : Environment) : String :=
  match env.find? `a with
  | some (.defnInfo d) => s!"a = {d.value}"
  | _ => "none"
def main (args : List String) : IO Unit := do
  let [root, v2] := args | throw <| IO.userError "usage"
  initSearchPath (← findSysroot)
  IO.println s!"first: {val (← importModules #[{module := `D}] {})}"
  IO.FS.writeBinFile (root ++ "/A.olean.new") (← IO.FS.readBinFile v2)
  IO.FS.rename (root ++ "/A.olean.new") (root ++ "/A.olean")
  IO.println s!"second: {val (← importModules #[{module := `D}] {})}"
END
cat > A2.lean <<'END'
def a : Nat := 2
END
run lean -o "$TMP_DIR/A2.olean" A2.lean
for mode in fast check; do
  setting=""
  [ "$mode" = check ] && setting=check
  cp "$LIB/A.olean" "$LIB/A.olean.orig"
  capture env LEAN_PATH="$LIB" LEAN_OLEAN_PACK="$TMP_DIR/cache.paperlean" \
    PAPERLEAN_IMPORT="$setting" lean --run Again.lean "$LIB" "$TMP_DIR/A2.olean"
  check_out_contains "first: a = OfNat.ofNat.{0} Nat 1 "
  check_out_contains "second: a = OfNat.ofNat.{0} Nat 2 "
  mv "$LIB/A.olean.orig" "$LIB/A.olean"
done
