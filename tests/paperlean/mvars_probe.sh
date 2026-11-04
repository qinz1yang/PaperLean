# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests the probe that lets `isDefEq` skip `instantiateMVars` (`src/paperlean/mvars_probe.cpp`): over
# unassigned, assigned and delayed-assigned metavariables (with the pending one assigned or not) and
# level metavariables, it says that `instantiateMVars` changes nothing exactly for the expressions
# that reach no assigned metavariable, and for these the result is the expression and the
# metavariable context is the same object.

cat > "$TMP_DIR/MVarsProbe.lean" <<'EOF2'
import Lean
open Lean Meta

run_meta do
  unless PaperLean.nativeAvailable (← getEnv) do
    throwError "PaperLean's native code is not available"
  let nat := mkConst ``Nat
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  assignLevelMVar v.mvarId! Level.one
  let a ← mkFreshExprMVar nat
  let b ← mkFreshExprMVar nat
  b.mvarId!.assign (mkNatLit 1)
  let c ← mkFreshExprMVar nat
  c.mvarId!.assign (mkApp (mkConst ``Nat.succ) b)
  let f ← mkFreshExprMVar (← mkArrow nat nat)
  -- `?d` and `?e`, delayed-assigned to `?p` (unassigned) and `?q` (assigned afterwards)
  let (d, e, q) ← withLocalDeclD `x nat fun x => do
    let p ← mkFreshExprMVar nat (kind := .syntheticOpaque)
    let q ← mkFreshExprMVar nat (kind := .syntheticOpaque)
    let d ← mkLambdaFVars #[x] p
    let e ← mkLambdaFVars #[x] q
    return (d.bindingBody!.getAppFn, e.bindingBody!.getAppFn, q)
  unless (← d.mvarId!.isDelayedAssigned) && (← e.mvarId!.isDelayedAssigned) do
    throwError "no delayed assignments"
  q.mvarId!.assign (mkNatLit 2)
  let add (x y : Expr) := mkApp2 (mkConst ``Nat.add) x y
  -- (expression, whether it reaches an assigned metavariable)
  let cases : List (Expr × Bool) := [
    (a, false), (b, true), (c, true), (nat, false),
    (mkApp f a, false), (mkApp f b, true), (mkApp d (mkNatLit 0), false), (mkApp e (mkNatLit 0), true),
    (mkSort u, false), (mkSort v, true), (mkSort (mkLevelMax u v), true),
    (mkConst ``List [u], false), (mkConst ``List [v], true),
    (add a a, false), (add a b, true), (add (mkApp d a) (mkApp f a), false), (add a (mkApp e a), true),
    (mkLambda `y .default (mkSort u) a, false), (mkLambda `y .default (mkSort v) a, true)]
  for (x, reaches) in cases do
    let mctx ← getMCtx
    let probe := PaperLean.mvarsInstantiated mctx x
    unless probe == !reaches do
      throwError "the probe says {probe} for {x}"
    let r ← instantiateMVars x
    if probe then
      unless r.equal x && unsafe ptrAddrUnsafe (← getMCtx) == ptrAddrUnsafe mctx do
        throwError "instantiateMVars changes {x}, which the probe skips"
  logInfo "ok"
EOF2
cd "$TMP_DIR"
capture_exit 0 lean MVarsProbe.lean
check_out_contains "ok"
