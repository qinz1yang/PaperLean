/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake.PaperLean.Cache

open System Lake.PaperLean

private def waitFor (file : FilePath) : IO Unit := do
  for _ in [:6000] do
    if ← file.pathExists then return
    IO.sleep 10
  throw <| IO.userError s!"timed out waiting for {file}"

-- Fake pack contents suffice here: the tested invariant is the allocator's directory ownership,
-- independently of packing modules. Every writer still takes the production cache and key locks.
private def writer (dir : FilePath) (name : String) (gate : FilePath) : IO Unit :=
  Cache.withCacheUse dir do
    let entry := s!"pack/{name}"
    Cache.withKeyLock dir entry do
      let tmp ← Cache.tempDir dir entry
      let pending := s!"pack/{tmp.fileName.getD ""}"
      IO.FS.createDirAll tmp
      IO.FS.writeFile (tmp / "pack.paperlean") name
      IO.FS.writeFile (gate / "started") ""
      let base ← Cache.reserveSlot dir pending 0x80000000
      IO.FS.writeFile (gate / "ready") s!"{← IO.Process.getPID}\n{pending}\n{base.toNat}\n"
      waitFor (gate / "release")
      Cache.publishPack dir pending entry 1
      IO.FS.writeFile (gate / "done") ""

private def failedPublish (dir : FilePath) (missing : Bool) : IO Unit :=
  Cache.withCacheUse dir do
    let entry := if missing then "pack/final" else "missing/final"
    Cache.withKeyLock dir entry do
      let tmp ← Cache.tempDir dir "pack/rollback"
      let pending := s!"pack/{tmp.fileName.getD ""}"
      IO.FS.createDirAll tmp
      unless missing do discard <| Cache.reserveSlot dir pending 1
      let result ← (Cache.publishPack dir pending entry 1).toBaseIO
      if result.isOk then throw <| IO.userError "publication unexpectedly succeeded"
      unless ← tmp.pathExists do throw <| IO.userError "failed publication removed the pending pack"
      IO.FS.writeFile (dir / "pending") pending

def main (args : List String) : IO Unit := do
  match args with
  | ["writer", dir, name, gate] => writer dir name gate
  | ["rename-fails", dir] => failedPublish dir false
  | ["missing-slot", dir] => failedPublish dir true
  | _ => throw <| IO.userError "expected writer, rename-fails or missing-slot"
