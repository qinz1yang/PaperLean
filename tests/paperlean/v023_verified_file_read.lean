/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.PaperLean.OLeanPack
import Lean.PaperLean.NativeLibs

open Lean.PaperLean

def main : IO Unit := do
  let path := "subject"
  let expected := "verified bytes\n".toUTF8
  let some id ← fileIdentity path | throw <| IO.userError "missing input identity"
  let hash := OLeanPack.hashBytes expected
  unless hash.length == 32 do throw <| IO.userError "missing content digest"
  unless (← OLeanPack.readVerifiedBytes path id hash) == expected do
    throw <| IO.userError "regular read changed the bytes"
  unless (← OLeanPack.readVerifiedBytes path id "") == expected do
    throw <| IO.userError "identity-only read changed the bytes"
  let .error _ ← (OLeanPack.readVerifiedBytes path id (OLeanPack.hashBytes "other".toUTF8)).toBaseIO
    | throw <| IO.userError "accepted wrong digest"
  let .error _ ← (OLeanPack.readVerifiedBytes path ByteArray.empty hash).toBaseIO
    | throw <| IO.userError "accepted missing identity"
  let some emptyId ← fileIdentity "empty" | throw <| IO.userError "missing empty file"
  unless (← OLeanPack.readVerifiedBytes "empty" emptyId (OLeanPack.hashBytes .empty)).isEmpty do
    throw <| IO.userError "empty file returned data"
  let owned := "cache/owned"
  let some ownedId ← OLeanPack.ownedFileIdentity owned | throw <| IO.userError "missing owned file"
  unless (← OLeanPack.readVerifiedOwnedBytes owned ownedId hash) == expected do
    throw <| IO.userError "regular owned read changed the bytes"
  IO.FS.writeFile "ready" ""
  for _ in [:500] do
    if ← System.FilePath.pathExists "replaced" then break
    IO.sleep 20
  unless ← System.FilePath.pathExists "replaced" do throw <| IO.userError "replacement timed out"
  -- The final symlink points to the exact original inode with its original identity.
  unless (← fileIdentity owned) == some ownedId do throw <| IO.userError "original identity changed"
  unless (← OLeanPack.readVerifiedBytes owned ownedId hash) == expected do
    throw <| IO.userError "workspace artifact symlink rejected"
  unless (← OLeanPack.ownedFileIdentity owned).isNone do throw <| IO.userError "owned symlink stamped"
  let .error _ ← (OLeanPack.readVerifiedOwnedBytes owned ownedId hash).toBaseIO
    | throw <| IO.userError "owned reader followed a substituted symlink"
  let .error _ ← (OLeanPack.readVerifiedBytes path id hash).toBaseIO
    | throw <| IO.userError "accepted substituted FIFO"
  IO.println "regular and empty files verified, substituted FIFO rejected"
