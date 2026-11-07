import Std.Async.ContextAsync

open Std Std.Async

private def check (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw <| .userError message

private def scopeExit (fail : Bool) : IO Unit := do
  let saved ← IO.mkRef (none : Option CancellationContext)
  let result ← (Async.block <| ContextAsync.run do
    saved.set (some (← ContextAsync.getContext))
    if fail then throw <| .userError "scope failed"
    pure 42).toBaseIO
  check (if fail then result matches .error _ else result matches .ok 42) "scope result changed"
  let some ctx ← saved.get | throw <| .userError "missing scope context"
  check (← ctx.isCancelled) "scope context survived its exit"
  IO.ofExcept (← IO.wait (← ctx.done))
  check ((← ctx.countAliveTokens) == 0) "scope retained live children"

private def backgroundExit : IO Unit := do
  let parent ← CancellationContext.new
  let _ : Nonempty CancellationContext := ⟨parent⟩
  let seen ← IO.Promise.new
  Async.block <| ContextAsync.runIn parent <| ContextAsync.background (α := Unit) do
    seen.resolve (← ContextAsync.getContext)
    throw <| .userError "background failed"
  let some child ← IO.wait seen.result? | throw <| .userError "background never started"
  IO.ofExcept (← IO.wait (← child.done))
  check (!(← parent.isCancelled)) "background failure cancelled its parent"
  check ((← parent.countAliveTokens) == 1) "background failure retained a child"
  parent.cancel .cancel

private def concurrentScopes : IO Unit := do
  let parent ← CancellationContext.new
  for n in [:128] do
    let result ← Async.block <| ContextAsync.runIn parent <|
      ContextAsync.concurrentlyAll #[(pure n : ContextAsync Nat), pure (n + 1)]
    check (result == #[n, n + 1]) "concurrentlyAll changed result ordering"
    check ((← parent.countAliveTokens) == 1) "concurrentlyAll retained its group"
  let result ← (Async.block <| ContextAsync.runIn parent <|
    ContextAsync.concurrentlyAll #[(throw (.userError "child failed") : ContextAsync Nat), pure 7]).toBaseIO
  check (result matches .error _) "concurrentlyAll dropped an exception"
  check ((← parent.countAliveTokens) == 1) "failed concurrentlyAll retained its group"
  let empty ← Async.block <| ContextAsync.runIn parent <|
    ContextAsync.concurrentlyAll (#[] : Array (ContextAsync Nat))
  check (empty.isEmpty && (← parent.countAliveTokens) == 1) "empty concurrentlyAll retained its group"
  parent.cancel .cancel

private def concurrentPairFailure : IO Unit := do
  let parent ← CancellationContext.new
  let result ← (Async.block <| ContextAsync.runIn parent <|
    ContextAsync.concurrently (pure 7 : ContextAsync Nat)
      (throw (.userError "pair failed") : ContextAsync Nat)).toBaseIO
  check (result matches .error _) "concurrently dropped an exception"
  check ((← parent.countAliveTokens) == 1) "failed concurrently retained its group"
  parent.cancel .cancel

private def raceScope (fail : Bool) : IO Unit := do
  let parent ← CancellationContext.new
  let _ : Nonempty CancellationContext := ⟨parent⟩
  let sibling ← parent.fork
  let started ← IO.Promise.new
  let exited ← IO.Promise.new
  let slow : ContextAsync Nat := do
    let ctx ← ContextAsync.getContext
    started.resolve ctx
    ContextAsync.awaitCancellation
    exited.resolve ()
    pure 9
  let fast : ContextAsync Nat := do
    let _ ← await started
    if fail then throw <| .userError "race failed first"
    pure 42
  let result ← (Async.block <| ContextAsync.runIn parent <| ContextAsync.raceAll #[slow, fast]).toBaseIO
  check (if fail then result matches .error _ else result matches .ok 42) "race arbitration changed"
  let some loser ← IO.wait started.result? | throw <| .userError "race loser never started"
  check (← loser.isCancelled) "race did not cancel its loser"
  let _ ← IO.wait exited.result?
  check (!(← parent.isCancelled) && !(← sibling.isCancelled)) "local race cancelled unrelated work"
  check ((← parent.countAliveTokens) == 2) "local race retained its group"
  parent.cancel .cancel

private def noncooperativeLoser : IO Unit := do
  let parent ← CancellationContext.new
  let _ : Nonempty CancellationContext := ⟨parent⟩
  let started ← IO.Promise.new
  let release ← IO.Promise.new
  let exited ← IO.Promise.new
  let slow : ContextAsync Nat := do
    started.resolve (← ContextAsync.getContext)
    let _ ← await release
    exited.resolve ()
    pure 9
  let fast : ContextAsync Nat := do
    let _ ← await started
    pure 42
  let result ← Async.block <| ContextAsync.runIn parent <| ContextAsync.raceAll #[slow, fast]
  -- Reaching here must not require the loser to observe cancellation or terminate.
  release.resolve ()
  let _ ← IO.wait exited.result?
  check (result == 42 && !(← parent.isCancelled)) "race waited for or escaped its local group"
  parent.cancel .cancel

private def emptyRace : IO Unit := do
  let parent ← CancellationContext.new
  let result ← (Async.block <| ContextAsync.runIn parent <|
    ContextAsync.raceAll (#[] : Array (ContextAsync Nat))).toBaseIO
  check (result matches .error _) "empty race did not fail"
  check (!(← parent.isCancelled) && (← parent.countAliveTokens) == 1) "empty race leaked or cancelled parent"
  parent.cancel .cancel

private def parentCancellation : IO Unit := do
  let parent ← CancellationContext.new
  let entered ← IO.Promise.new
  let branch : ContextAsync Nat := do
    entered.resolve ()
    ContextAsync.awaitCancellation
    pure 5
  let task ← (ContextAsync.runIn parent <| ContextAsync.raceAll #[branch]).asTask
  let _ ← IO.wait entered.result?
  parent.cancel .shutdown
  check ((← IO.ofExcept (← IO.wait task)) == 5) "parent cancellation did not reach race group"

def main : IO Unit := do
  scopeExit false
  scopeExit true
  backgroundExit
  concurrentScopes
  concurrentPairFailure
  raceScope false
  raceScope true
  noncooperativeLoser
  emptyRace
  parentCancellation
