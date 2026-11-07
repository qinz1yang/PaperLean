/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.CompactedRegion

open Lean System

/-- Independent compactor instances may save to the same pathname concurrently. -/
unsafe def main (args : List String) : IO Unit := do
  let [path, version] := args | throw (IO.userError "expected a directory and format")
  let dir := FilePath.mk path
  IO.FS.createDirAll dir
  let out := dir / "shared.olean"
  let v3 := version == "v3"
  let mut inputs := #[]
  let mut valid := #[]
  for i in [:8] do
    let contents := Array.replicate (32768 + i) (i + 7)
    let ref := dir / s!"{i}.olean"
    discard <| CompactedRegion.save ref `Tiny contents #[] none v3
    valid := valid.push (← IO.FS.readBinFile ref)
    inputs := inputs.push contents
  let ready : IO.Promise Unit ← IO.Promise.new
  let mut writers := #[]
  for contents in inputs do
    writers := writers.push (← IO.asTask (prio := .dedicated) do
      discard <| IO.wait ready.result?
      for _ in [:4] do discard <| CompactedRegion.save out `Tiny contents #[] none v3)
  ready.resolve ()
  for writer in writers do discard <| IO.ofExcept (← IO.wait writer)
  let bytes ← IO.FS.readBinFile out
  unless valid.any (· == bytes) do throw (IO.userError "compacted output mixes writers")
  let (restored, region) ← CompactedRegion.read (α := Array Nat) out #[]
  unless inputs.contains restored do throw (IO.userError "could not restore any original compacted array")
  CompactedRegion.free region
  if (← dir.readDir).any (·.fileName.startsWith "shared.olean.tmp") then
    throw (IO.userError "writer leaked a temporary")
  let failed := dir / "bad"
  IO.FS.createDirAll failed
  IO.FS.writeFile (failed / "child") "keep"
  unless (← (CompactedRegion.save failed `Tiny inputs[0]! #[] none v3).toBaseIO) matches .error .. do
    throw (IO.userError "published over a nonempty directory")
  unless (← IO.FS.readFile (failed / "child")) == "keep" do throw (IO.userError "failed rename lost data")
  if (← dir.readDir).any (·.fileName.startsWith "bad.tmp") then throw (IO.userError "failed rename leaked a temporary")
