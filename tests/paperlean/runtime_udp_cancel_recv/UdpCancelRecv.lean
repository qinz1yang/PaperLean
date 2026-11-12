import Std.Internal.UV.UDP
import Init.System.Platform

open Std.Internal.UV Std.Net
open System

private def fdDir : FilePath :=
  if System.Platform.isOSX then "/dev/fd" else "/proc/self/fd"

private def fdCount : IO Nat := do
  return (← fdDir.readDir).size

private def cancelCycle : IO Unit := do
  let s ← UDP.Socket.new
  let _p ← s.recv 1024
  s.cancelRecv

/--
Each pending `recv` takes a reference that the event loop owns while the operation
is pending; `cancelRecv` stops the operation, so it must release that reference.
Otherwise the socket's finalizer never runs and its descriptor leaks.  The test
warms up the event loop, then measures the descriptor count across 100
recv/cancelRecv cycles.
-/
def main : IO Unit := do
  cancelCycle
  IO.sleep 100
  let before ← fdCount
  for _ in List.range 100 do
    cancelCycle
  IO.sleep 500
  let after ← fdCount
  IO.println s!"fd count: {before} -> {after}"
  unless after <= before + 5 do
    throw <| IO.userError s!"cancelRecv leaked {after - before} descriptors over 100 cycles"
