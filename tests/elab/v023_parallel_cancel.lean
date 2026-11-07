import Lean
import Lean.Elab.Parallel

open Lean Meta Elab Tactic

-- Each winning job returns a child task that observes its inherited cancellation token.
-- Cancelling the winner after it returns would also cancel this still-live child.
private def winner : CoreM (IO.Promise Unit × Task (CoreM Bool)) := do
  let release ← IO.Promise.new (α := Unit)
  let child ← Core.CoreM.asTask' do
    let _ ← IO.wait release.result!
    let some token := (← read).cancelTk? | throwError "missing child token"
    token.isSet
  return (release, child)

private def checkWinner (result : IO.Promise Unit × Task (CoreM Bool)) : CoreM Unit := do
  result.1.resolve ()
  if ← result.2.get then throwError "parFirst cancelled the winning job's child"

run_meta do
  checkWinner (← Core.CoreM.parFirst [winner])
  checkWinner (← MetaM.parFirst [winner])
  Term.TermElabM.run' do
    checkWinner (← Term.TermElabM.parFirst [winner])

example : True := by
  run_tac do
    checkWinner (← TacticM.parFirst [winner])
  trivial
