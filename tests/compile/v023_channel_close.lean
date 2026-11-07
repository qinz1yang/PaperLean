import Std.Sync.Channel
import Std.Sync.Broadcast

open Std Std.Async Std.Async.IO

private def check (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw <| .userError message

private def channelClose (n : Nat) : IO Unit := do
  let ch ← CloseableChannel.new (α := Nat) (some 1)
  check ((← IO.wait (← ch.send 0)) matches .ok ()) "initial send failed"
  let pending ← (Array.range n).mapM fun i => ch.send (i + 1)
  discard <| ch.close
  -- No receive is allowed to be needed to wake any blocked producer.
  for task in pending do
    check ((← IO.wait task) matches .error .closed) "blocked sender did not fail on close"
  check ((← ch.tryRecv) == some 0) "close discarded buffered value"
  check ((← ch.tryRecv) == none) "close added an unbuffered value"

private def broadcastClose (n subscribers : Nat) : IO Unit := do
  let ch ← Broadcast.new (α := Nat) 1
  let receivers ← (Array.range subscribers).mapM fun _ => ch.subscribe
  check ((← IO.wait (← ch.send 0)) matches .ok _) "initial broadcast failed"
  let pending ← (Array.range n).mapM fun i => ch.send (i + 1)
  ch.close
  for task in pending do
    check ((← IO.wait task) matches .error _) "blocked broadcast sender did not fail on close"
  for receiver in receivers do
    check ((← receiver.tryRecv) == some 0) "close discarded buffered broadcast"
    check ((← receiver.tryRecv) == none) "close added an unbuffered broadcast"

private def broadcastWrite : IO Unit := do
  let ch ← Broadcast.new (α := Nat) 1
  Async.block <| AsyncWrite.write ch 0
  let r1 ← ch.subscribe
  let r2 ← ch.subscribe
  Async.block <| AsyncWrite.write ch 42
  check ((← r1.tryRecv) == some 42 && (← r2.tryRecv) == some 42) "write did not broadcast"
  ch.close
  let result ← (Async.block <| AsyncWrite.write ch 43).toBaseIO
  check (result matches .error _) "AsyncWrite suppressed a closed-channel error"

private def zeroCapacity : IO Unit := do
  let ch ← CloseableChannel.new (α := Nat) (some 0)
  let pending ← ch.send 9
  discard <| ch.close
  check ((← ch.tryRecv) == some 9) "zero-capacity drain contract changed"
  check ((← IO.wait pending) matches .ok ()) "zero-capacity send no longer drains"
  check ((← ch.tryRecv) == none) "zero-capacity value was delivered twice"

def main : IO Unit := do
  for n in [2, 128] do
    channelClose n
    broadcastClose n 1
    broadcastClose n 3
  broadcastWrite
  zeroCapacity
