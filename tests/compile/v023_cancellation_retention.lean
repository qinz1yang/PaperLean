import Std.Sync.CancellationContext

open Std

private def check (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw <| .userError message

private def rootSlots (ctx : CancellationContext) : IO Nat := do
  let st ← ctx.state.atomically get
  let some (_, children) := st.tokens.get? ctx.id | return 0
  pure children.size

private def checkCompacted (root : CancellationContext) : IO Unit := do
  let count ← root.countAliveTokens
  let st ← root.state.atomically get
  check (count == st.tokens.size) "incorrect live root count"
  for (_, (_, children)) in st.tokens do
    for child in children do
      check (st.tokens.contains child) "count retained a stale child ID"

private def churn (n : Nat) : IO Unit := do
  let parent ← CancellationContext.new
  for _ in [:n] do
    let child ← parent.fork
    let grandchild ← child.fork
    child.cancel .cancel
    check (← grandchild.isCancelled) "nested cancellation failed"
  -- Inspect before counting: the fork threshold itself must bound sequential history.
  let st ← parent.state.atomically get
  check (st.tokens.size == 1) "churn retained live tokens"
  check ((← rootSlots parent) ≤ 2) "fork compaction retained unbounded sequential history"
  checkCompacted parent
  check ((← rootSlots parent) == 0) "count did not remove the remaining stale IDs"
  parent.cancel .cancel

private def manySiblings : IO Unit := do
  let parent ← CancellationContext.new
  let children ← (Array.range 256).mapM fun _ => parent.fork
  for child in children[:224] do child.cancel .cancel
  -- After the live map shrinks, the next fork must remove the accumulated history.
  let newChild ← parent.fork
  let st ← parent.state.atomically get
  check ((← rootSlots parent) < 2 * st.tokens.size) "fork did not compact after live-map shrink"
  check ((← rootSlots parent) == 33) "fork lost a live child or retained stale IDs"
  newChild.cancel .cancel
  checkCompacted parent
  check ((← rootSlots parent) == 32) "count did not compact remaining history"
  check ((← parent.countAliveTokens) == 33) "incorrect live subtree count"
  parent.cancel .shutdown
  checkCompacted parent
  for child in children do
    check (← child.isCancelled) "root cancellation missed a child"

private def subtreeCount : IO Unit := do
  let root ← CancellationContext.new
  let left ← root.fork
  let right ← root.fork
  let children ← (Array.range 64).mapM fun _ => left.fork
  for child in children do child.cancel .cancel
  check ((← left.countAliveTokens) == 1) "subtree count included stale children"
  check ((← rootSlots left) == 0) "subtree count left historical IDs"
  check (!(← right.isCancelled)) "subtree count affected a sibling"
  checkCompacted root
  check ((← root.countAliveTokens) == 3) "subtree compaction lost live nodes"
  root.cancel .cancel

private def concurrentForkCancel : IO Unit := do
  let parent ← CancellationContext.new
  let gate ← IO.Promise.new
  let tasks ← (Array.range 8).mapM fun _ => IO.asTask (prio := .dedicated) do
    let _ ← IO.wait gate.result?
    for _ in [:128] do
      let child ← parent.fork
      let grandchild ← child.fork
      child.cancel .cancel
      check (← grandchild.isCancelled) "concurrent cancellation missed a descendant"
  gate.resolve ()
  parent.cancel .shutdown
  for task in tasks do IO.ofExcept (← IO.wait task)
  checkCompacted parent
  check ((← parent.countAliveTokens) == 0) "concurrent fork escaped cancellation"
  let child ← parent.fork
  check (← child.isCancelled) "fork of cancelled parent was live"

def main : IO Unit := do
  churn 256
  churn 512
  manySiblings
  subtreeCount
  concurrentForkCancel
