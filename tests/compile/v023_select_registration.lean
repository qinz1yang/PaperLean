import Std.Async.Select

open Std.Async

private def check (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw <| .userError message

private def single (win throwAfter : Bool) : IO Unit := do
  let cleanups ← IO.mkRef 0
  let selector : Selector Nat := {
    tryFn := pure none
    registerFn := fun waiter => do
      if win then
        waiter.race (pure ()) fun promise => promise.resolve (.ok 41)
      if throwAfter then throw <| .userError "registration failed"
    unregisterFn := cleanups.modify (· + 1)
  }
  let result ← (Async.block <| Selectable.one #[.case selector (fun n => pure (n + 1))]).toBaseIO
  if win then
    check (result matches .ok 42) "winning result was lost after registration"
  else
    check (result matches .error _) "registration error was lost"
  check ((← cleanups.get) == 1) "selector cleanup must run exactly once"

private def otherSelectorWins : IO Unit := do
  let first ← IO.mkRef (none : Option (Waiter Nat))
  let cleanups ← IO.mkRef 0
  -- Whichever selector is registered second resolves the first selector's waiter, then throws.
  -- This exercises a different winner regardless of the randomized registration order.
  let selector : Selector Nat := {
    tryFn := pure none
    registerFn := fun waiter => do
      let previous ← first.swap (some waiter)
      if let some previous := previous then
        previous.race (pure ()) fun promise => promise.resolve (.ok 7)
        throw <| .userError "losing registration failed"
    unregisterFn := do
      first.set none
      cleanups.modify (· + 1)
  }
  let result ← Async.block <| Selectable.one #[.case selector pure, .case selector pure]
  check (result == 7) "another selector's winning value was lost"
  check ((← cleanups.get) == 2) "both selectors must be cleaned up"

def main : IO Unit := do
  single true false
  single true true
  single false true
  otherSelectorWins
