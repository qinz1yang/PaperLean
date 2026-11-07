/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import all Lake.PaperLean.Prepare
import Lake.PaperLean.Cache
import Init.Data.ByteArray.Extra

open Lake Lean System

private structure OldHeader where
  path : String
  identity : Array UInt64
  imports : Array (Array String)
  deriving ToJson

private def forge (out source : FilePath) : IO Unit := do
  let source ← IO.FS.realPath source
  let some id ← Lean.PaperLean.fileIdentity source.toString | throw <| IO.userError "missing source identity"
  let identity := (Array.range (id.size/8)).map fun i => (id.extract (8*i) (8*(i+1))).toUInt64LE!
  -- Reproduce the exact legacy encoding and checksum, but claim the source imports unbuilt Dep.B.
  let rows : Array OldHeader := #[{path := source.toString, identity, imports := #[#["Dep","B"]]}]
  let build := Lake.PaperLean.Cache.buildName
  let digest := Lake.PaperLean.Cache.key #[build, (toJson rows).compress]
  IO.FS.writeFile out ((toJson (build, digest, rows)).compress ++ "\n")

private def publication (op : String) (dir target : FilePath) (image : String) : IO Unit := do
  let pid ← IO.Process.getPID
  let legacy := if op == "event" then dir / s!"probe-{pid}.json.tmp" else
    (Lake.PaperLean.imageReceipt (dir / image)).addExtension s!"tmp.{pid}"
  IO.FS.hardLink target legacy
  try
    if op == "event" then
      Lake.PaperLean.traceNativeRepairs "probe" #[]
      unless (← IO.FS.readFile (dir / s!"probe-{pid}.json")) == "[]\n" do
        throw <| IO.userError "repair event was not published"
    else
      unless ← Lake.PaperLean.checkImportImage dir (some image) do throw <| IO.userError "failed to verify test image"
      unless ← Lake.PaperLean.importImageUsable dir (some image) do throw <| IO.userError "receipt is unusable"
    unless (← IO.FS.readFile target) == "external" && (← legacy.pathExists) do
      throw <| IO.userError "publication modified a pre-existing temporary name or its external hardlink"
  finally
    discard <| (IO.FS.removeFile legacy).toBaseIO

public def main (args : List String) : IO Unit := do
  match args with
  | ["forge", out, src] => forge out src
  | ["event", dir, target] => publication "event" dir target ""
  | ["image", dir, target, image] => publication "image" dir target image
  | ["receipt", dir, image] =>
    if ← Lake.PaperLean.importImageUsable dir (some image) then throw <| IO.userError "accepted a FIFO receipt"
  | ["supported", source] => IO.println (← Lean.PaperLean.readableSourceIdentity source).isSome
  | ["cache", workspace] =>
    let some cache ← Lake.PaperLean.Cache.root? | throw <| IO.userError "unavailable cache"
    let real ← IO.FS.realPath workspace
    IO.println (Lake.PaperLean.Cache.buildDir cache / Lake.PaperLean.Cache.sourceInputEntry real.toString)
  | _ => throw <| IO.userError "unexpected arguments"
