import Init.System.IO

private def check (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw <| .userError message

private def capture (script : String) (input? : Option String := none) : IO IO.Process.Output :=
  IO.Process.output { cmd := "sh", args := #["-c", script] } input?

private def expectError (action : IO α) : IO Unit := do
  let result ← action.toBaseIO
  check (result matches .error _) "expected an IO error"

def main : IO Unit := do
  let spaces := String.ofList (List.replicate 1048576 ' ')
  let input := String.ofList (List.replicate 1048576 'x')
  let out ← capture "printf '%1048576s'; cat" (some input)
  check (out.exitCode == 0 && out.stdout == spaces ++ input && out.stderr == "")
    "stdout-first capture lost data"
  let out ← capture "printf '%1048576s' >&2; cat" (some input)
  check (out.exitCode == 0 && out.stdout == input && out.stderr == spaces)
    "stderr-first capture lost data"
  let out ← capture "cat" (some input)
  check (out.exitCode == 0 && out.stdout == input && out.stderr == "") "large echo failed"
  for input? in [none, some ""] do
    let out ← capture "cat; printf eof; printf err >&2" input?
    check (out.exitCode == 0 && out.stdout == "eof" && out.stderr == "err")
      "empty input did not deliver EOF"
  let out ← capture "exit 7"
  check (out.exitCode == 7 && out.stdout == "" && out.stderr == "") "exit status changed"
  expectError <| capture "exit 7" (some input)
  -- EOF on one output pipe reveals invalid UTF-8 while the other pipe stays open.
  -- exec keeps the waiting process at the child PID, inside the test harness's process group.
  -- Cleanup must terminate it instead of waiting for the other reader first.
  expectError <| capture "printf '\\377'; exec 1>&-; exec sleep 30"
