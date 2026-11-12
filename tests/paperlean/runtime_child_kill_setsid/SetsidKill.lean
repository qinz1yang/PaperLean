import Init.System.IO

private def check (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw <| IO.userError message

private partial def waitForMarker (path : String) (rounds : Nat) : IO Bool := do
  if rounds == 0 then return false
  try
    discard <| IO.FS.readFile path
    return true
  catch _ =>
    IO.sleep 5
    waitForMarker path (rounds - 1)

/--
Spawn a child that asks for `setsid`, wait until the preloaded library has reached the
delayed `setsid()` call in the forked child (so the child is alive and still belongs to
the parent's process group), then kill it.  On 0.2.3 `killpg(pid, SIGKILL)` fails with
ESRCH because the child has not created its group yet, and `Child.kill` reports an error.
-/
def main (args : List String) : IO Unit := do
  let marker ← match args with
    | [marker] => pure marker
    | _ => throw <| IO.userError "expected marker path"
  let child ← IO.Process.spawn {
    cmd := "/bin/true", setsid := true
    stdin := .null, stdout := .null, stderr := .null }
  unless ← waitForMarker marker 2000 do
    throw <| IO.userError "child never reached setsid"
  let killed : Except IO.Error Unit ← child.kill.toBaseIO
  let code ← child.wait
  IO.println s!"kill={killed} code={code}"
  check (killed matches .ok ()) "Child.kill failed before the child's setsid()"
  check (code == 137) "child did not die from SIGKILL"
