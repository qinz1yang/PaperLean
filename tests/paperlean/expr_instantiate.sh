# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests `instantiate` and `instantiateRange` in PaperLean's native code (`src/paperlean/replace.cpp`,
# `Lean.PaperLean.exprInstantiate`) and `Lean.PaperLean.betaRev`, which `whnf` uses: for the bodies
# under the leading binders of the types of the constants of `Init`, `Std` and `Lean` and the values
# of their definitions, substituted by free variables and by terms with loose bound variables (which
# are lifted under binders), they give the expressions of the kernel's functions; so does `betaRev`
# of these types and values applied to fewer and more arguments than their leading binders.

cat > "$TMP_DIR/ExprInstantiate.lean" <<'EOF2'
module

import all Lean.Meta.WHNF
import Lean
open Lean

def body? : Expr → Option Expr
  | .forallE _ _ b _ | .lam _ _ b _ => some b
  | _ => none

/-- The bodies of `e` under its first and its first three leading binders. -/
def bodies (e : Expr) : List Expr :=
  let b1 := body? e
  let b3 := b1.bind body? |>.bind body?
  b1.toList ++ b3.toList

run_cmd do
  unless PaperLean.nativeAvailable (← getEnv) do
    throwError "PaperLean's native code is not available"
  let substs : List (Array Expr) := [
    #[mkFVar ⟨`x⟩, mkFVar ⟨`y⟩, mkFVar ⟨`z⟩],
    #[.bvar 0, mkApp (.bvar 2) (.bvar 0), mkLambda `a .default (mkConst ``Nat) (.bvar 1)]]
  let mut checked : Nat := 0
  let mut differ : Array Name := #[]
  for (c, info) in (← getEnv).constants.map₁.toList do
    let es := [info.type] ++ (if info matches .defnInfo _ then info.value?.toList else [])
    for e in es do
      for b in bodies e do
        for s in substs do
          checked := checked + 1
          -- (`equal`: `==` does not see binder names and annotations)
          unless (PaperLean.exprInstantiate b s).equal (b.instantiate s) &&
              (PaperLean.exprInstantiateRange b 1 3 s).equal (b.instantiateRange 1 3 s) do
            differ := differ.push c
      for s in substs do
        for n in [1, 2, 3] do
          let args := s.extract 0 n
          for preserveMData in [false, true] do
            unless (PaperLean.betaRev e args preserveMData).equal (e.betaRev args (preserveMData := preserveMData)) do
              differ := differ.push c
  unless differ.isEmpty do
    throwError "different results for {differ.size} constants, e.g. {differ.toList.take 5}"
  unless checked > 100000 do
    throwError "too few expressions checked: {checked}"
  logInfo "ok"
EOF2
cd "$TMP_DIR"
capture_exit 0 lean ExprInstantiate.lean
check_out_contains "ok"
