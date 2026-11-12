/-
`PaperLean.TCCache.getInstancesUnify` promises to count no heartbeats: it saves the counter and
restores it after the cache work. If `getUnify`/`getUnifyRootKey` throws (here `isDefEqStuck`), the
restore must still run, or a retry in the same command is charged for the cache's work.
-/
import Lean.PaperLean.TCCache

open Lean Meta

/-- A reducible definition: `DiscrTree.getUnifyRootKey`/`getUnify` on `R ?m` with
`isDefEqStuckEx` reaches the stuck branch before it can return a key. -/
@[reducible] def R (α : Type) : Type := α

run_meta do
  withConfig (fun c => { c with isDefEqStuckEx := true }) do
    let m ← mkFreshExprMVar (mkSort 1)
    let ty := mkApp (mkConst ``R) m
    PaperLean.envStartRecording
    -- Heartbeats count allocations: the same `try`/`catch` around a bare `isDefEqStuck` throw is what
    -- the caller itself allocates, which the hook may not exceed.
    let c0 ← IO.getNumHeartbeats
    let ctrl ← try
      (Meta.throwIsDefEqStuck : MetaM Unit)
      pure false
    catch _ =>
      pure true
    let c1 ← IO.getNumHeartbeats
    let h0 ← IO.getNumHeartbeats
    let threw ← try
      discard <| PaperLean.TCCache.getInstancesUnify ty
      pure false
    catch _ =>
      pure true
    let h1 ← IO.getNumHeartbeats
    discard <| PaperLean.envStopRecording
    IO.println s!"threw {threw}, counted {h1 - h0}, control {c1 - c0}"
    unless ctrl && threw && h1 - h0 ≤ c1 - c0 do
      throwError s!"the throwing cache hook counted {h1 - h0} heartbeats (a bare throw: {c1 - c0})"
