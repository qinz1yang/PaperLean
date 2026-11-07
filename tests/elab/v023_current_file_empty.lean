import Lean

open Lean Meta LibrarySuggestions

run_meta do
  let g := (← mkFreshExprMVar (mkConst ``True)).mvarId!
  let env ← getEnv
  let name := `pendingSuggestionTheorem
  let async ← env.addConstAsync name .thm
  let thm : TheoremVal := { name, type := mkConst ``True, value := mkConst ``True.intro, levelParams := [], all := [name] }
  async.commitSignature thm.toConstantVal
  let .ok final := async.asyncEnv.addDeclCore 2000000 1024 (.thmDecl thm) none | throwError "kernel rejected control theorem"
  let entered ← IO.Promise.new (α := Unit)
  let done ← IO.Promise.new (α := Unit)
  let released ← IO.mkRef false
  let unlock ← IO.asTask (prio := .dedicated) do
    discard <| IO.wait entered.result?
    -- A regression unblocks after the watchdog and fails the assertion below.
    for _ in [:1000] do
      if ← done.isResolved then break
      IO.sleep 2
    released.set true
    async.commitCheckEnv final
  entered.resolve ()
  let rs ← withEnv async.mainEnv <| currentFile g {
    maxSuggestions := 0
    filter := fun _ => throwError "an empty query must never call its filter" }
  let stillPending := !(← released.get)
  done.resolve ()
  let .ok () := unlock.get | throwError "worker failed"
  unless rs.isEmpty && stillPending && (async.mainEnv.checked.get.find? name).isSome do
    throwError "zero-budget suggestions waited for a pending kernel check or returned a suggestion"
