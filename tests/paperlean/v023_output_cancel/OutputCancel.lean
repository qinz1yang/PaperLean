import Init.System.IO

@[extern "u08_oracle_arm"] private opaque arm (observe : Bool) : BaseIO Bool
@[extern "u08_oracle_observer"] private opaque enteredExitWait (pid : UInt32) : BaseIO Bool
@[extern "u08_oracle_reaped"] private opaque wasReaped (pid : UInt32) : BaseIO Bool

private def checkWaitAny : IO Unit := do
  let entered ← IO.Promise.new (α := Unit)
  let gate ← IO.Promise.new (α := Nat)
  let task ← BaseIO.asTask do
    entered.resolve ()
    IO.waitAny [gate.result!]
  discard <| IO.wait entered.result!
  IO.cancel task
  gate.resolve 37
  unless (← IO.wait task) == 37 do
    throw <| IO.userError "ordinary waitAny lost its independently completed result"

def main (args : List String) : IO Unit := do
  let [python, helper, mode, fifo] := args | throw <| IO.userError "expected python helper mode fifo"
  let closed := mode == "closed"
  unless closed || mode == "blocked" do throw <| IO.userError "bad phase"
  unless ← arm closed do throw <| IO.userError "could not arm process observer"
  checkWaitAny
  let input? := if closed then none else some (String.ofList (List.replicate 2097152 'x'))
  let task ← IO.asTask <| IO.Process.output { cmd := python, args := #[helper, mode, fifo] } input?
  let receipt ← IO.FS.Handle.mk fifo .read
  let line ← receipt.getLine
  let some pid := line.trimAscii.toString.toNat? | throw <| IO.userError s!"bad child PID: {line}"
  unless pid > 0 && pid < 2147483648 do throw <| IO.userError "PID out of range"
  if closed then
    unless ← enteredExitWait pid.toUInt32 do throw <| IO.userError "no blocking wait for this PID"
  IO.cancel task
  match ← IO.wait task with
  | .error (.interrupted cmd 0 details) =>
    unless cmd == python && details == "process output task canceled" do
      throw <| IO.userError s!"wrong interrupted error: {cmd} {details}"
  | .error err => throw <| IO.userError s!"unexpected process error: {err}"
  | .ok _ => throw <| IO.userError "canceled output returned success"
  unless ← wasReaped pid.toUInt32 do throw <| IO.userError "owned child is live or waitable"
  IO.println s!"{mode}: interrupted and reaped"
