import Init.System.IO

def main : IO Unit := do
  let tasks ← (List.range 8).mapM fun _ => IO.asTask do
    IO.Process.output { cmd := "sh", args := #["-c", "printf out; printf err >&2"] }
  for task in tasks do
    let out ← IO.ofExcept task.get
    unless out.stdout == "out" && out.stderr == "err" && out.exitCode == 0 do
      throw <| IO.userError "output differs"
  pure ()
