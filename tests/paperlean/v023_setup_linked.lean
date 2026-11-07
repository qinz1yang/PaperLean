/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Setup

open Lean Lean.PaperLean Lean.PaperLean.SetupIndex System

private def row (name : Name) (imports : Array LinkedImport := #[]) : LinkedRecord :=
  {name, root := "/library", isModule := true, imports}

private def imp (name : Name) (target : Option RecordRef) (all := false) : LinkedImport :=
  {module := name, target, importAll := all, isExported := true, isMeta := false}

private def writeBytes (dir : FilePath) (bytes : ByteArray) : IO FilePath := do
  let path := dir / linkedFileName bytes.hash
  IO.FS.writeBinFile path bytes
  return path

private def load (dir file : FilePath) (name : Name) (record := 0) : IO ModuleSetup := do
  let setup : ModuleSetup := {name, importArts := ({} : NameMap _).insert .anonymous (reference file record)}
  let path := dir / "module.setup.json"
  IO.FS.writeFile path (setupToJsonCompact setup).compress
  ModuleSetup.load path

private def rejected (act : IO ModuleSetup) : IO Unit := do
  if (← act.toBaseIO).isOk then throw <| IO.userError "accepted an invalid setup"

private def promotion (dir : FilePath) : IO Unit := do
  let edge := fun (i : Nat) (all exported isMeta : Bool) => {target := i, importAll := all, isExported := exported, isMeta : Edge}
  let baseRows : Array Record := #[
    {name := `Hidden, root := 0, isModule := true, imports := #[]},
    {name := `Bridge, root := 0, isModule := true, imports := #[edge 0 false false false]},
    {name := `Core, root := 0, isModule := true, imports := #[edge 1 false false false]}]
  let base := encode #["/library"] baseRows
  IO.FS.writeBinFile (dir / fileName base) base
  let core := RecordRef.base base.hash 2
  let left := encodeLinked (row `Left #[imp `Core (some core) true])
  let right := encodeLinked (row `Right #[imp `Core (some core)])
  discard <| writeBytes dir left
  discard <| writeBytes dir right
  let root := row `Root #[imp `Left (some (.node left.hash)) true,
    {imp `Right (some (.node right.hash)) with isMeta := true}]
  let result ← load dir (← writeBytes dir (encodeLinked root)) `Root
  let flat := encode #["/library"] (baseRows ++ #[
    {name := `Left, root := 0, isModule := true, imports := #[edge 2 true true false]},
    {name := `Right, root := 0, isModule := true, imports := #[edge 2 false true false]},
    {name := `Root, root := 0, isModule := true, imports := #[edge 3 true true false, edge 4 false true true]}])
  let flatFile := dir / fileName flat
  IO.FS.writeBinFile flatFile flat
  let expected ← load dir flatFile `Root 5
  unless (artifactsToJson result.importArts).compress == (artifactsToJson expected.importArts).compress &&
      result.importArts.contains `Hidden && (result.importArts.find? `Core).any (·.oleanPrivate?.isSome) do
    throw <| IO.userError "combined meta/import-all promotion differs from the v1 graph"

def main (args : List String) : IO Unit := do
  let [dir] := args | throw <| IO.userError "expected a temporary directory"
  let dir : FilePath := dir
  IO.FS.createDirAll dir
  let base := encode #["/library"] #[
    {name := `Leaf, root := 0, isModule := true, imports := #[]}]
  let baseRef := RecordRef.base base.hash 0
  IO.FS.writeBinFile (dir / fileName base) base
  let middle := encodeLinked (row `Mid #[imp `Leaf (some baseRef) true])
  let midFile ← writeBytes dir middle
  let root := encodeLinked (row `Root #[imp `Mid (some (.node middle.hash)) true, imp `External none])
  let rootFile ← writeBytes dir root
  let setup ← load dir rootFile `Root
  unless (setup.importArts.find? `Leaf).map (·.toArrays) == some (artifactsAt "/library" `Leaf true true).toArrays &&
      (setup.importArts.find? `Mid).map (·.toArrays) == some (artifactsAt "/library" `Mid true true).toArrays &&
      !setup.importArts.contains `External && !setup.importArts.contains .anonymous do
    throw <| IO.userError "linked import visibility differs"
  -- A v1 reference is still read directly by the original path.
  unless (← load dir (dir / fileName base) `Leaf).importArts.isEmpty do throw <| IO.userError "v1 changed"
  rejected (load dir rootFile `Other)
  rejected (load dir rootFile `Root 1)
  let wrongName ← writeBytes dir (encodeLinked (row `Root #[imp `NotLeaf (some baseRef)]))
  rejected (load dir wrongName `Root)
  let wrongIndex ← writeBytes dir (encodeLinked (row `Root #[imp `Leaf (some (.base base.hash 5))]))
  rejected (load dir wrongIndex `Root)
  let bytes := encodeLinked (row `Root #[imp `External none])
  let truncated ← writeBytes dir (bytes.extract 0 (bytes.size - 1))
  rejected (load dir truncated `Root)
  let trailing ← writeBytes dir (bytes.push 0)
  rejected (load dir trailing `Root)
  let badTag ← writeBytes dir (bytes.set! (bytes.size - 1) 3)
  rejected (load dir badTag `Root)
  let badFlags ← writeBytes dir (bytes.set! (bytes.size - 2) 8)
  rejected (load dir badFlags `Root)
  IO.FS.writeBinFile midFile (encodeLinked (row `Mid))
  rejected (load dir rootFile `Root)
  IO.FS.removeFile midFile
  rejected (load dir rootFile `Root)
  -- Lean accepts quoted identifiers such as «Late\Leaf» on POSIX. The module name
  -- is used for its artifact path; the node containing it is opened by digest.
  let special := Name.str .anonymous "Late\\Leaf"
  let quoted := encodeLinked (row special)
  discard <| writeBytes dir quoted
  let parent ← writeBytes dir <| encodeLinked (row `Root #[imp special (some (.node quoted.hash))])
  unless (← load dir parent `Root).importArts.contains special do throw <| IO.userError "lost quoted name"
  promotion dir
  IO.println "linked setup checks passed"
