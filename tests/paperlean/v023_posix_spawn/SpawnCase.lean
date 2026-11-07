import Init

@[extern "u06_posix_close_stdio"] opaque closeStdio (mask : UInt32) : IO Bool
@[extern "u06_posix_buffer_mark"] opaque bufferMark : IO Unit
@[extern "u06_posix_flush_mark"] opaque flushMark : IO Unit

private def stream : String → IO.Process.Stdio
  | "P" => .piped
  | "N" => .null
  | _ => .inherit

private def edits (path : String) : Array (String × Option String) :=
  #[("PATH", some "unused"), ("U06_JOIN", some "first"), ("U06_JOIN", none),
    ("PATH", some path), ("U06_JOIN", some "last"), ("U06_DROP", none)]

private def expect (ok : Bool) (msg : String) : IO Unit := do
  unless ok do throw <| IO.userError msg

def main (args : List String) : IO Unit := do
  match args with
  | ["streams", cmd, cwd, report, mask, i, o, e, path, inherit] =>
    expect (← closeStdio mask.toNat!.toUInt32) "could not close test stdio"
    let child ← IO.Process.spawn {
      cmd, cwd := some cwd, args := #[report, "two words"]
      stdin := stream i, stdout := stream o, stderr := stream e, env := edits path
      inheritEnv := inherit == "1", setsid := true }
    expect ((← child.wait) == 0) "descriptor reporter failed"
  | ["lookup", cwd, shell] =>
    let inherited ← IO.Process.output {cmd := "sh", args := #["-c", "printf '%s' \"$U06_PARENT\""]}
    expect (inherited.exitCode == 0 && inherited.stdout == "inherited") "unmodified inheritance failed"
    let text ← IO.Process.output {
      cmd := "plain", cwd := some cwd, args := #["two words"]
      env := edits "bad:good", inheritEnv := false}
    if shell == "yes" then
      expect (text.exitCode == 0 && text.stdout == "two words:last\n") "libc shell fallback changed"
    else
      expect (text.exitCode == 255 && text.stderr == "could not execute external process 'plain'\n")
        "libc ENOEXEC behavior changed"
    let defaultPath ← IO.Process.output {
      cmd := "sh", args := #["-c", "printf default-path"]
      env := #[("PATH", none)], inheritEnv := false}
    expect (defaultPath.exitCode == 0 && defaultPath.stdout == "default-path") "default PATH failed"
    let denied ← IO.Process.output {cmd := "denied", cwd := some cwd, env := edits "bad"}
    expect (denied.exitCode == 255 && denied.stderr == "could not execute external process 'denied'\n")
      "permission-denied search failure changed"
  | ["failure", cwd] =>
    bufferMark
    let child ← IO.Process.spawn {
      cmd := "no-such-u06-program", cwd := some cwd
      stdin := .null, stdout := .inherit, stderr := .piped, env := edits "missing", inheritEnv := false}
    let err ← child.stderr.readToEnd
    expect ((← child.wait) == 255 && err == "could not execute external process 'no-such-u06-program'\n")
      "exec failure status/diagnostic changed"
    let missing := cwd ++ "/missing-dir"
    let child ← IO.Process.spawn {
      cmd := "/bin/sh", cwd := some missing
      stdin := .null, stdout := .inherit, stderr := .piped}
    let err ← child.stderr.readToEnd
    expect ((← child.wait) == 255 && err == s!"could not change directory to {missing}\n")
      "chdir failure status/diagnostic changed"
    flushMark
  | ["open-failure"] =>
    let child ← IO.Process.spawn {cmd := "/bin/sh", args := #["-c", "exit 0"], stdin := .null}
    expect ((← child.wait) == 255) "failed child null open did not terminate"
  | ["dup-failure"] =>
    let child ← IO.Process.spawn {cmd := "/bin/sh", args := #["-c", "exit 0"], stdout := .null}
    expect ((← child.wait) == 255) "failed child dup2 did not terminate"
  | _ => throw <| IO.userError "invalid test case"
