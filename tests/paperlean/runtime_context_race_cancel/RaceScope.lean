import Std.Async.ContextAsync

open Std Std.Async

private def check (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw <| IO.userError message

/-- Wait briefly for the context cleanup that follows the race result.  On 0.2.3 the
loser's wrapper context and its explicit context stay alive while the loser is blocked,
so the count can never reach one. -/
private partial def waitForOnlyParent (parent : CancellationContext) (rounds : Nat) : IO Nat := do
  let alive ← parent.countAliveTokens
  if alive == 1 || rounds == 0 then return alive
  IO.sleep 20
  waitForOnlyParent parent (rounds - 1)

/-- Race a noncooperative loser against an immediately successful winner.
`winnerFirst` selects whether the winner is the first or second argument.  The
loser blocks on `release`, so it cannot clean up its own context before the
check.  The only live context after `race` returns must be the parent. -/
private def raceCase (winnerFirst : Bool) : IO Unit := do
  let parent ← CancellationContext.new
  let _ : Nonempty CancellationContext := ⟨parent⟩
  let started ← IO.Promise.new
  let release ← IO.Promise.new (α := Unit)
  let loser : ContextAsync Nat := do
    started.resolve (← ContextAsync.getContext)
    let _ ← await release
    pure 9
  let winner : ContextAsync Nat := pure 42
  try
    let result ← Async.block <| ContextAsync.runIn parent <|
      if winnerFirst then ContextAsync.race winner loser
      else ContextAsync.race loser winner
    let some _ ← IO.wait started.result? | throw <| IO.userError "loser never started"
    let alive ← waitForOnlyParent parent 100
    IO.println s!"winnerFirst={winnerFirst} result={result} alive={alive}"
    check (result == 42) "race returned the wrong result"
    check (alive == 1) s!"race retained live contexts: {alive}"
  finally
    release.resolve ()
    IO.sleep 100
    parent.cancel .cancel

def main : IO Unit := do
  raceCase false
  raceCase true
