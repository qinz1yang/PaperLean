import Lean

@[extern "lean_internal_set_thread_stack_size"]
opaque stackSize (sz : USize) : BaseIO Unit
@[extern "lean_paperlean_start_import_fold"]
opaque startFold (name : @& Lean.Name) (act : BaseIO (Except IO.Error Nat)) :
    BaseIO (Option (Task (Except IO.Error Nat)))
@[extern "lean_paperlean_release_import_worker"]
opaque releaseSlot : BaseIO Unit

def main : IO Unit := do
  let calls ← IO.mkRef 0
  let act : IO Nat := do
    try
      calls.modify (· + 1)
      return 42
    finally releaseSlot
  -- The test runs in its own process. The runtime adds its 128 KiB guard to this
  -- unsigned value, giving pthread_attr_setstacksize a zero size on Darwin and Linux.
  stackSize (0 - 128 * 1024)
  let declined ← startFold `Fixture act.toBaseIO
  stackSize (8 * 1024 * 1024)
  unless declined.isNone && (← calls.get) == 0 do
    throw <| IO.userError "a failed launch ran the speculative action"
  let some recovered ← startFold `Fixture act.toBaseIO
    | throw <| IO.userError "the failed launch retained its worker slot"
  unless (← IO.ofExcept (← IO.wait recovered)) == 42 && (← calls.get) == 1 do
    throw <| IO.userError "the next speculative action did not run exactly once"
  IO.println "recovered"
