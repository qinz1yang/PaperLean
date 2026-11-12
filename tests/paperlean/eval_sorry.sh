# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests `evalConst` of an imported declaration that uses `sorry`: `run_boxed` reads the
# `sorryDep?` of the same `IR.Decl` it passes to the interpreter (`decl_sorry_dep` in
# `src/library/ir_interpreter.cpp`). The error must be Lean's (which blames `sorryAx` here, as rc3
# does) and the same with the faster import, with `PAPERLEAN_IMPORT=legacy` and under
# `PAPERLEAN_IMPORT=check`.

SRC="$TMP_DIR/src"
LIB="$TMP_DIR/lib"
mkdir -p "$SRC" "$LIB"
cd "$SRC"

cat > A.lean <<'END'
def bad : Nat := by sorry
END
run env LEAN_PATH="$LIB" lean -o "$LIB/A.olean" A.lean

cat > Use.lean <<'END'
import Lean
import A
open Lean
#eval show CoreM Unit from do
  let env ← getEnv
  let opts ← getOptions
  match unsafe env.evalConst Nat opts `bad with
  | .ok n => IO.println s!"eval ok: {n}"
  | .error e => IO.println s!"eval error: {e}"
END
for mode in legacy "" check; do
  capture env LEAN_PATH="$LIB" PAPERLEAN_IMPORT="$mode" lean Use.lean
  check_out_contains "eval error: cannot evaluate code because 'sorryAx' uses 'sorry' and/or contains errors"
  cp "$CAPTURED.out.produced" "$TMP_DIR/sorry.$mode.out"
done
for mode in "" check; do
  $DIFF -- "$TMP_DIR/sorry.legacy.out" "$TMP_DIR/sorry.$mode.out" ||
    fail "the sorry error with PAPERLEAN_IMPORT=$mode differs from the legacy import"
done
