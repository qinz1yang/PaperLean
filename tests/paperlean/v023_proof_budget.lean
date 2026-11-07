/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

open Lean
@[extern "paperlean_test_proof_budget"]
opaque runBatch (env : Kernel.Environment) (normal ambient spent : USize) (decls : @& Array Declaration)
    (cancel parent : @& Option IO.CancelToken) : Except Kernel.Exception Kernel.Environment

@[extern "paperlean_test_stock_proof_cost"]
opaque stockCost (env : Kernel.Environment) (decl : @& Declaration) : USize

@[extern "paperlean_test_cancel_poll"]
opaque cancelPoll (tk : @& IO.CancelToken) : BaseIO UInt8

inductive Outcome where
  | success | kernelError | timeout | interrupted
  deriving BEq, Repr

def classify : Except Kernel.Exception Kernel.Environment → Outcome
  | .ok _ => .success
  | .error .deterministicTimeout => .timeout
  | .error .interrupted => .interrupted
  | .error _ => .kernelError

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Init}] {}
  let parent ← IO.CancelToken.new
  parent.set
  unless (← cancelPoll parent) == 7 do
    throw <| IO.userError "concurrent cancellation read lost the set flag"
  let live ← IO.CancelToken.new
  let yes := Declaration.thmDecl {
    name := `trialBudgetOK
    levelParams := []
    type := mkConst ``True
    value := mkConst ``True.intro }
  let no := Declaration.thmDecl {
    name := `trialBudgetBad
    levelParams := []
    type := mkConst ``False
    value := mkConst ``True.intro }
  let test (name : String) (normal ambient spent : USize) (decl : Declaration)
      (tk : Option IO.CancelToken) (expected : Outcome) : IO Unit := do
    let actual := classify (runBatch env.toKernelEnv normal ambient spent #[decl] tk (some parent))
    unless actual == expected do throw <| IO.userError s!"{name}: expected {repr expected}, got {repr actual}"
  test "accepted" 2000 4000 137 yes (some live) .success
  test "invalid" 2000 4000 137 no none .kernelError
  test "normal limit has one tick left" 101 10000 100 yes none .timeout
  test "ambient limit has one tick left" 10000 101 100 yes none .timeout
  test "normal exhausted" 100 0 101 yes none .timeout
  test "ambient exhausted" 0 100 101 yes none .timeout
  test "independent trial cap" 0 0 12000001 yes none .success
  test "cancelled stock check" 2000 4000 137 yes (some parent) .interrupted
  test "cancelled exhausted budget" 100 100 101 yes (some parent) .interrupted
  let second := Declaration.thmDecl {
    name := `trialBudgetSecond
    levelParams := []
    type := mkConst ``True
    value := mkConst ``True.intro }
  let useFirst := Declaration.thmDecl {
    name := `trialUsesFirst
    levelParams := []
    type := mkConst ``True
    value := mkConst `trialBudgetOK }
  let base := env.toKernelEnv
  let maxOne := max (stockCost base yes) (stockCost base second)
  let batch (normal : USize) (ds : Array Declaration) (tk : Option IO.CancelToken := none) :=
    runBatch base normal 0 0 ds tk (some parent)
  unless classify (batch maxOne #[yes]) == .success && classify (batch maxOne #[second]) == .success &&
      classify (batch maxOne #[yes, second]) == .timeout do
    throw <| IO.userError "declarations did not share their kernel budget"
  let .ok extended := batch 0 #[yes, useFirst] | throw <| IO.userError "dependent batch rejected"
  unless (extended.find? `trialBudgetOK).isSome && (extended.find? `trialUsesFirst).isSome &&
      (base.find? `trialBudgetOK).isNone && (base.find? `trialUsesFirst).isNone do
    throw <| IO.userError "batch result did not own the expected environment"
  let .error (.unknownConstant _ n) := batch 0 #[useFirst, yes] |
    throw <| IO.userError "first stock error changed"
  unless n == `trialBudgetOK do throw <| IO.userError "wrong missing prerequisite"
  unless classify (batch 0 #[]) == .kernelError && classify (batch 0 #[] (some parent)) == .interrupted do
    throw <| IO.userError "empty proof batch accepted or cancellation lost"
  IO.println "proof trial budgets ok"
