/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Setup

open Lean System Lean.PaperLean Lean.PaperLean.SetupIndex

def node (n : Nat) : Name := Name.str .anonymous s!"M{n}"

def fixture (size : Nat) : Array Record :=
  (Array.range size).map fun i => {
    name := node i, root := 0, isModule := true
    imports := match i with
      | 0 => #[{ target := 1, importAll := true, isExported := true, isMeta := false }]
      | 1 => #[{ target := 2, importAll := false, isExported := true, isMeta := true }]
      | 2 => #[{ target := 3, importAll := false, isExported := false, isMeta := false }]
      | _ => #[] }

def emit (dir : FilePath) (size : Nat) (receipt : Bool) : IO Unit := do
  if size < 4 then throw <| IO.userError "fixture requires at least four records"
  IO.FS.createDirAll dir
  let bytes := encode #["/exact/library/root"] (fixture size)
  let file := dir / fileName bytes
  if receipt then
    unless ← publish file.toString bytes do throw <| IO.userError "demand publisher is unavailable"
  else IO.FS.writeBinFile file bytes
  let ix ← IO.ofExcept (Index.read file bytes)
  let arts ← IO.ofExcept (ix.importArts (node 0) 0)
  let moved := artifactsAt "/nondefault/lake/selection" (node 1) true true
  let refs : NameMap ImportArtifacts := ({} : NameMap ImportArtifacts).insert .anonymous (reference file 0)
  let setup : ModuleSetup := {
    name := node 0, isModule := true
    importArts := refs.insert (node 1) moved }
  let setupFile := dir / s!"setup-{size}.json"
  IO.FS.writeFile setupFile (setupToJsonCompact setup).compress
  IO.FS.writeFile (setupFile.addExtension "expected") (artifactsToJson (arts.insert (node 1) moved)).compress
  IO.println file
  IO.println setupFile

-- Exercise the production descriptor guards without introducing a production pause hook.
opaque Descriptor : Type := Unit
@[extern "lean_paperlean_setup_index_open"]
opaque openDescriptor (file : @& String) : IO (Option (Descriptor × ByteArray))
@[extern "lean_paperlean_setup_index_record"]
opaque readDescriptor (index : @& Descriptor) (i : @& Nat) : IO ByteArray
@[extern "lean_paperlean_setup_index_check"]
opaque checkDescriptor (index : @& Descriptor) : IO Unit
@[extern "lean_paperlean_setup_index_close"]
opaque closeDescriptor (index : @& Descriptor) : BaseIO Unit

def held (file gate : FilePath) (read : Bool) : IO Unit := do
  let some (handle, _) ← openDescriptor file.toString
    | throw <| IO.userError "fixture has no valid receipt"
  try
    IO.FS.writeFile (gate / "opened") ""
    let mut released := false
    for _ in [0:1200] do
      if ← (gate / "release").pathExists then released := true; break
      IO.sleep 50
    unless released do throw <| IO.userError "descriptor gate timed out"
    if read then discard <| readDescriptor handle 0
    checkDescriptor handle
  finally closeDescriptor handle

def main (args : List String) : IO Unit := do
  match args with
  | ["emit", dir, size, mode] => emit dir size.toNat! (mode == "receipt")
  | ["read", setup] => IO.println (artifactsToJson (← ModuleSetup.load setup).importArts).compress
  | ["held", file, gate, mode] => held file gate (mode == "read")
  | _ => throw <| IO.userError "expected emit/read/held"
