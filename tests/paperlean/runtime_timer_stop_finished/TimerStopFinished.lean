import Std.Internal.UV.Timer

open Std.Internal.UV

private def check (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw <| IO.userError message

/--
`Timer.stop` is documented as a no-op on a finished timer, and `Timer.next` on a
finished one-shot timer must keep returning the promise created by the first
`next`.  In 0.2.3 stop clears the promise even when the timer is finished, so
the following next returns a fresh unresolved promise and any waiter hangs.
-/
def main : IO Unit := do
  let t ← Timer.mk 10 false
  let p ← t.next
  let r ← IO.wait p.result?
  check r.isSome "the first timer promise never fired"
  t.stop
  let p2 ← t.next
  let resolved ← p2.isResolved
  IO.println s!"first promise resolved: {r.isSome}"
  IO.println s!"after stop, next returns a resolved promise: {resolved}"
  check resolved "Timer.stop discarded a finished timer's resolved promise"
