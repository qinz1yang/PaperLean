import Init.System.IO

open System

@[extern "v023_windows_new_event"] private opaque newEvent : IO UInt64
@[extern "v023_windows_event_set"] private opaque eventSet (event : UInt64) : IO Bool
@[extern "v023_windows_close_event"] private opaque closeEvent (event : UInt64) : IO Unit
@[extern "v023_windows_mask_std"] private opaque maskStd (mask : UInt8) (invalid : Bool) : IO Unit
@[extern "v023_windows_restore_std"] private opaque restoreStd : IO Unit
@[extern "v023_windows_test_directory"] private opaque testDirectory (path : @& FilePath) (remove : Bool) : IO Unit

private def checkOutput (args : IO.Process.SpawnArgs) (input : Option String := none) : IO IO.Process.Output := do
  let out ← IO.Process.output args input
  unless out.exitCode == 0 do throw <| IO.userError s!"child {args.args} exited {out.exitCode}: {out.stderr}"
  return out

private def checkArgv (helper : String) : IO Unit := do
  discard <| checkOutput {
    cmd := helper
    args := #["argv", "", "two words", "a\tb", "path\\", "two\\\\", "a\\\"b", "a\\\\\"b", "\"",
      "*?", "line\nfeed", "λ🧪", "last"] }
  let tooLong := String.ofList (List.replicate 32767 'x')
  match ← (IO.Process.output {cmd := helper, args := #[tooLong]}).toBaseIO with
  | .error _ => pure ()
  | .ok _ => throw <| IO.userError "oversized command line accepted"

private def checkEnvironment (helper : String) : IO Unit := do
  let large (c : Char) := String.ofList (List.replicate 16000 c)
  discard <| checkOutput {
    cmd := helper
    args := #["environment"]
    env := #[("V023_REMOVE", none), ("V023_MIXED", some "first"), ("v023_mixed", some "last"),
      ("V023_TEXT", some "λ🧪"), ("V023_A", some (large 'a')), ("V023_B", some (large 'b')),
      ("V023_C", some (large 'c')), ("V023_TAIL", some "present")] }
  discard <| checkOutput {
    cmd := helper
    args := #["isolated"]
    inheritEnv := false
    env := #[("V023_ONLY", some "yes")] }
  discard <| checkOutput {cmd := helper, args := #["empty"], inheritEnv := false}
  for key in ["", "INVALID=NAME"] do
    let request : IO.Process.SpawnArgs := {
      cmd := helper
      args := #["empty"]
      env := #[(key, some "value")] }
    match ← (IO.Process.output request).toBaseIO with
    | .error _ => pure ()
    | .ok _ => throw <| IO.userError "invalid environment key was accepted"

private def checkHandle (helper : String) : IO Unit := do
  let event ← newEvent
  try
    discard <| checkOutput {cmd := helper, args := #["handle", toString event]}
    if ← eventSet event then throw <| IO.userError "child signalled the parent's unrelated inheritable event"
  finally
    closeEvent event

private def checkStdio (helper : String) : IO Unit := do
  let output ← checkOutput {cmd := helper, args := #["stdio"]} (some "ping")
  unless output.stdout == "pong" && output.stderr == "error" do
    throw <| IO.userError "child stdio redirection changed"

private def checkAbsent (helper : String) : IO Unit := do
  let some dir := (FilePath.mk helper).parent | throw <| IO.userError "expected an absolute probe path"
  let gui := (dir / "absent.exe").toString
  let event ← newEvent
  try
    -- A GUI child observes the actual missing slots without console auto-attachment.
    for (layout, mask) in [("000", 7), ("0NN", 1), ("NNN", 0)] do
      let request : IO.Process.SpawnArgs := {
        cmd := gui
        stdin := if layout == "NNN" then .null else .inherit
        stdout := if layout == "000" then .inherit else .null
        stderr := if layout == "000" then .inherit else .null
        env := #[("V023_STD_LAYOUT", some layout), ("V023_STD_EVENT", some (toString event))] }
      maskStd mask false
      try
        let child ← IO.Process.spawn request
        let exitCode ← child.wait
        unless exitCode == 0 do throw <| IO.userError s!"GUI stdio {layout} exited {exitCode}"
        if ← eventSet event then throw <| IO.userError s!"GUI stdio {layout} inherited the unrelated event"
      finally
        restoreStd
    -- An explicitly invalid handle must still fail instead of becoming an absent slot.
    maskStd 1 true
    try
      match ← (IO.Process.spawn {cmd := gui}).toBaseIO with
      | .error _ => pure ()
      | .ok child =>
        discard <| child.wait
        throw <| IO.userError "invalid standard handle was accepted"
    finally
      restoreStd
  finally
    closeEvent event

private def extendedPath (path : FilePath) : FilePath :=
  let name := path.normalize.toString
  if name.startsWith "\\\\?\\" then path else
  if let some unc := name.dropPrefix? "\\\\" then ⟨"\\\\?\\UNC\\" ++ unc.copy⟩
  else ⟨"\\\\?\\" ++ name⟩

private def checkCwd (helper : String) : IO Unit := do
  let some base := (FilePath.mk helper).parent | throw <| IO.userError "expected an absolute probe path"
  let original ← IO.Process.getCurrentDir
  let dirs ← IO.mkRef ([] : List FilePath)
  let make (p : FilePath) : IO Unit := do
    testDirectory p false
    dirs.modify (p :: ·)
  let short := (base / "λ🧪").normalize
  try
    make short
    IO.Process.setCurrentDir short
    unless (← IO.Process.getCurrentDir).normalize == short do throw <| IO.userError "Unicode cwd did not round-trip"
    discard <| checkOutput {cmd := helper, args := #["cwd", short.toString], cwd := some short}
    IO.Process.setCurrentDir original
    let mut plain := short
    for i in [:3] do
      plain := plain / (String.ofList (List.replicate 90 'x') ++ toString i)
      make (extendedPath plain)
    unless plain.toString.length > 260 do throw <| IO.userError "long cwd fixture too short"
    let extended := extendedPath plain
    IO.Process.setCurrentDir extended
    let actual := (← IO.Process.getCurrentDir).normalize
    unless actual == extended.normalize || actual == plain.normalize do
      throw <| IO.userError s!"long cwd truncated: {actual}"
  finally
    IO.Process.setCurrentDir original
    for dir in ← dirs.get do testDirectory dir true
  unless (← IO.Process.getCurrentDir) == original do throw <| IO.userError "original cwd not restored"

def main (args : List String) : IO Unit := do
  let [helper, mode] := args | throw <| IO.userError "expected probe.exe and test mode"
  match mode with
  | "argv" => checkArgv helper
  | "environment" => checkEnvironment helper
  | "handles" => checkHandle helper
  | "stdio" => checkStdio helper
  | "absent" => checkAbsent helper
  | "cwd" => checkCwd helper
  | _ => throw <| IO.userError s!"unknown test mode: {mode}"
