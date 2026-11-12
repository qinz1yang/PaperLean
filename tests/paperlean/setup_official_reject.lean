/-
An indexed side setup (`<module>.setup.paperlean`, written by `PaperLean.moduleSetup`) is not a
valid official `ModuleSetup`: official Lean cannot resolve the anonymous index reference and
would silently drop the selected artifacts, then fall back to `LEAN_PATH`. Its decoder must
reject the file, while PaperLean's compact decoder must still read the reference.
-/
import Lean.Setup

open Lean

def sideSetup : ModuleSetup :=
  { name := `M
    importArts := ({} : NameMap ImportArtifacts).insert .anonymous
      (PaperLean.SetupIndex.reference "/nonexistent/setup-0.paperlean" 0) }

def main (args : List String) : IO UInt32 := do
  let side := PaperLean.setupToJsonCompact sideSetup
  match args with
  | ["write", file] =>
    IO.FS.writeFile file side.compress
    return 0
  | [] =>
    -- the decoder of official Lean (`ModuleSetup.load` calls `fromJson?`)
    if (fromJson? side : Except String ModuleSetup).isOk then
      throw <| IO.userError "official ModuleSetup decoder accepted an indexed side setup"
    match PaperLean.setupFromJsonCompact? side with
    | .ok decoded =>
      unless decoded.importArts.contains .anonymous do
        throw <| IO.userError "PaperLean's decoder lost the index reference"
    | .error e =>
      throw <| IO.userError s!"PaperLean's decoder rejected its own indexed side setup: {e}"
    IO.println "indexed side setups are rejected by the official decoder and read by PaperLean"
    return 0
  | _ =>
    throw <| IO.userError "usage: setup_official_reject.lean [write FILE]"
