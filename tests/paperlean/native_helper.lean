/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.PaperLean.NativeLibs
import Lean.PaperLean.OLeanPack

/-!
What the tests of native libraries need beyond what `paperlean prepare` does, for `lean --run` (the
modules are found in `LEAN_PATH`):
- `manifest <out> <library> <directory of the .c files> <module>...` writes the manifest of a library
  compiled by the test: its modules are analysed and their files hashed in this process, and the `.c`
  files are the modules'.
- `manifest-events <events> <out> <library> <directory> <module>...` reads the evaluation events
  from a separate `evalImpuritiesMain` process.
- `check <module>...` prints those of the modules that are not known to be pure, with the reason.
- `unread` does that for a module that cannot be read.
-/

open Lean Lean.PaperLean

/-- What `paperlean prepare`'s analysis says about `modules`, in this process. -/
def evalVerdicts (modules : Array (Name × System.FilePath)) : IO EvalVerdicts := do
  let verdicts ← IO.mkRef ({} : EvalVerdicts)
  evalImpuritiesSafe modules (← searchPathRef.get) (← getLibDir (← getBuildDir)) {}
    fun line => verdicts.modify (·.add line)
  verdicts.get

/-- The modules of `evalVerdicts` that are not known to be pure, with the reason. -/
def impurities (modules : Array (Name × System.FilePath)) : IO (Array (System.FilePath × String)) := do
  let v ← evalVerdicts modules
  return v.impure ++ (modules.filter fun (_, f) => !v.certified.contains f && !v.impure.any (·.1 == f)).map
    fun (_, f) => (f, "there is no verdict about it")

/-- Writes to `out` the manifest of the native library `lib` of `modules`, each with its `.c` file. The
files of the modules are found in the search path, as importing them finds them, and must be those the
`.c` files were generated with. -/
def writeManifest (out lib : String) (modules : Array (Name × String))
    (events? : Option System.FilePath := none) : IO Unit := do
  let record : System.FilePath := s!"{out}.hashes"
  let mods ← modules.mapM fun (m, c) => do
    let olean ← findOLean m
    let paths ← (moduleFiles olean).mapM fun f => return if ← f.pathExists then f.toString else ""
    let parts := #[olean] ++ (#[1, 2].filterMap fun i =>
      if paths[i]! != "" then some (moduleFiles olean)[i]! else none)
    let hashes ← paths.mapM fun p => do
      if p.isEmpty then return ""
      return (← OLeanPack.hashFiles #[p] #[] record 1)[0]!.2
    return { name := m, cFile := c, hashes, data := ← moduleNativeData parts : NativeManifestModule }
  if ← record.pathExists then IO.FS.removeFile record
  let oleans ← modules.mapM (findOLean ·.1)
  let verdicts ← match events? with
    | none => evalVerdicts (modules.map (·.1) |>.zip oleans)
    | some f => do
      let lines ← IO.FS.lines f
      pure <| lines.foldl EvalVerdicts.add ({} : EvalVerdicts)
  -- as they are now, which is what the manifest records
  let ids ← (oleans.mapM moduleIdentities : BaseIO _)
  let mods := (mods.zip oleans).zip ids |>.map fun ((m, f), i) =>
    { m with data.differs := m.data.differs || verdicts.certified[f]? != some i }
  discard <| writeNativeManifestFiles out lib #[] mods #[]
  if (← (oleans.mapM moduleIdentities : BaseIO _)) != ids then
    IO.FS.removeFile out
    throw <| IO.userError "the files of a module changed while its manifest was written"

def report (bad : Array (System.FilePath × String)) : IO Unit := do
  for (f, why) in bad do IO.println s!"impure {f.fileName.get!}: {why}"
  IO.println s!"bad={bad.size}"

def main (args : List String) : IO Unit := do
  match args with
  | "manifest" :: out :: lib :: dir :: mods =>
    writeManifest out lib (mods.map fun m => (m.toName, s!"{dir}/{m}.c")).toArray
    IO.println "manifest written"
  | "manifest-events" :: events :: out :: lib :: dir :: mods =>
    writeManifest out lib (mods.map fun m => (m.toName, s!"{dir}/{m}.c")).toArray (some ⟨events⟩)
  | "check" :: mods =>
    report (← impurities (← mods.toArray.mapM fun n => return (n.toName, ← findOLean n.toName)))
  | ["unread"] => report (← impurities #[(`Nope, "nope.olean")])
  | _ => throw <| IO.userError "unknown command"
