/--
Check that `IO.FS.realPath` preserves the error kind and errno reported by
realpath(3).  The caller passes pairs "kind\tpath"; kinds are `inappropriateType`
(ENOTDIR, 20) and `permissionDenied` (EACCES, 13).
-/
private def check (kind path : String) : IO Unit := do
  try
    let r ← IO.FS.realPath path
    throw <| IO.userError s!"{kind}: realPath unexpectedly succeeded with {r}"
  catch e =>
    match kind, e with
    | "inappropriateType", .inappropriateType _ 20 _ =>
        IO.println s!"{kind}: preserved error code 20"
    | "permissionDenied", .permissionDenied _ 13 _ =>
        IO.println s!"{kind}: preserved error code 13"
    | _, _ =>
        throw <| IO.userError s!"{kind}: wrong realPath error: {e}"

def main (args : List String) : IO Unit := do
  match args with
  | [notDir, permission] =>
      check "inappropriateType" notDir
      if permission.isEmpty then
        IO.println "permissionDenied: skipped (running as root)"
      else
        check "permissionDenied" permission
  | _ => throw <| IO.userError "expected <not-a-directory-child> <unreadable-child>"
