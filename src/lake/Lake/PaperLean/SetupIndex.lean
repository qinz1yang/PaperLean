/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lake.Config.Module
public import Lake.Config.Workspace
import Init.System.Promise
import Init.While
import Lake.PaperLean.Env
import Lean.PaperLean.System
import Std.Data.HashMap.Basic

/-!
The setup index of a build under `paperlean` commands (`accelerated`). Lake lists the artifacts of
every transitive import in the setup of each module that it compiles (`Lake.Module.buildLean`),
which takes time and space quadratic in the size of the library. Here the setup refers to the
module's record in an index of the modules whose headers the build has read (`note`), with their
package's library directory, whether they are a `module`, and their imports; `Lean.ModuleSetup.load`
computes the artifacts from the index as Lake does, with the files at their default location
(`Lean.PaperLean.SetupIndex`). That is where Lake has them unless they come from its artifact cache
(`noteArtifacts`): the setups of their importers list those. The headers are buffered until an
index is needed, so a build that compiles nothing does not construct the index.

An index is written when a module is compiled whose transitive imports the build's indexes do not
all have (`indexFor`), with all modules noted by then: once, unless compiles start before the build
has read the headers of the imports of the modules it compiles. Its file is named by the hash of its
contents, in a directory of the build (`buildDir`, `.lake/paperlean-setup/<process id>`), and is not
changed once there: builds that run at the same time have their own. The indexes are removed at the
end of the build (`finish`; not with `PAPERLEAN_SETUP_INDEX_KEEP`, for tests), or, if it was
interrupted, by the next build (`start`).
-/

open System Lean
open Lean.PaperLean.SetupIndex (artifactsAt encode fileName noModule unknown)

namespace Lake.PaperLean.SetupIndex

/-- A module whose header the build read. -/
structure Entry where
  name : Name
  /-- The library directory of its package. -/
  root : String
  isModule : Bool
  /-- Its imports, and whether a package of the workspace has the module of each. -/
  imports : Array (Import × Bool)
  deriving Inhabited

structure State where
  /-- Deferred header producers, latest first. -/
  pending : List (Unit → Option Entry) := []
  entries : Array Entry := #[]
  byName : Std.HashMap Name Nat := {}
  /-- Per entry, if computed: one more than the greatest entry among it and its transitive imports
  (`reachOf`). -/
  reach : Array Nat := #[]
  /-- The indexes of the build: the number of entries each has, and its file once written. -/
  written : Array (Nat × IO.Promise (Option FilePath)) := #[]
  /-- The modules whose artifacts are not where the index has them. -/
  moved : NameSet := {}
  deriving Inhabited

private builtin_initialize stateRef : IO.Ref State ← IO.mkRef {}

/-- The directory of the indexes of the builds of the workspace in `wsDir`. -/
def indexesDir (wsDir : FilePath) : FilePath :=
  wsDir / ".lake" / "paperlean-setup"

/-- The directory of the indexes of this build. -/
def buildDir (wsDir : FilePath) : BaseIO FilePath :=
  return indexesDir wsDir / toString (← IO.Process.getPID)

/-- Starts a build of the workspace in `wsDir`: removes the indexes of builds that were
interrupted. -/
public def start (wsDir : FilePath) : BaseIO Unit := do
  stateRef.set {}
  unless ← accelerated do return
  let .ok entries ← (indexesDir wsDir).readDir.toBaseIO | return
  for d in entries do
    if let some pid := d.fileName.toNat? then
      unless ← Lean.PaperLean.processAlive pid.toUInt32 do
        discard <| (IO.FS.removeDirAll d.path).toBaseIO

/-- Defers the header of `mod` until an index needs it, including its owner, library directory and
imports. The header is kept if imports of its name get it (`Workspace.findModule?`). -/
@[noinline, nospecialize] public def note {α : Type}
    (ws : Workspace) (mod : Module) (isModule : Bool)
    (imports : Array α) (toImport : α → Import × Bool) : BaseIO Unit := do
  let entry : Unit → Option Entry := fun _ =>
    if (ws.findModule? mod.name).any (·.pkg.keyName == mod.pkg.keyName) then
      some { name := mod.name, root := mod.pkg.leanLibDir.toString, isModule,
             imports := imports.map toImport }
    else none
  stateRef.modify fun s => { s with pending := entry :: s.pending }

/-- Notes the files of `mod` that `Module.computeExportInfo` gives its importers, its `.olean`
parts and its IR files, if they are not where the index has them, by `note` with `isModule`. -/
public def noteArtifacts (mod : Module) (isModule : Bool) (files : Array FilePath) :
    BaseIO Unit := do
  unless ← accelerated do return
  let atDefault := artifactsAt mod.pkg.leanLibDir mod.name isModule true
  unless files.map toString == atDefault.toArrays.flatten.map toString do
    stateRef.modify fun s => { s with moved := s.moved.insert mod.name }

/-- The modules whose artifacts are not where the index has them. -/
public def moved : BaseIO NameSet :=
  stateRef.modifyGet fun s => (s.moved, s)

/-- The value of `State.reach` of an entry with a transitive import that has no entry. -/
private def never : Nat := 1 <<< 32

/-- Adds the pending headers in the order noted, keeping the first of each name. The shared state
buffers them so a build that compiles nothing does not copy the index's arrays for every header. -/
private def State.drain (s : State) : State := Id.run do
  if s.pending.isEmpty then return s
  let pending := s.pending.reverse
  let size := s.entries.size
  let mut entries := s.entries
  let mut byName := s.byName
  let s := { s with pending := [], entries := #[], byName := {} }
  for makeEntry in pending do
    let some entry := makeEntry () | continue
    unless byName.contains entry.name do
      let i := entries.size
      entries := entries.push entry
      byName := byName.insert entry.name i
  -- A missing import may now have its header; complete closures keep the same indices.
  let reach := if entries.size == size then s.reach else
    s.reach.map fun r => if r ≥ never then 0 else r
  return { s with entries, byName, reach }

/-- `State.reach` of entry `i`, computed for it and its transitive imports. -/
private def State.reachOf (s : State) (i : Nat) : Nat × State := Id.run do
  let inProgress := never + 1
  let mut reach := s.reach
  let s := { s with reach := #[] }
  reach := reach ++ .replicate (s.entries.size - reach.size) 0
  let mut stack := #[i]
  while h : 0 < stack.size do
    let j := stack.back
    if reach[j]! != 0 && reach[j]! != inProgress then
      stack := stack.pop
      continue
    reach := reach.set! j inProgress
    let imports := s.entries[j]!.imports.filterMap fun (imp, isLocal) =>
      if isLocal then some (s.byName[imp.module]?) else none
    if let some (some c) := imports.find? (·.any (reach[·]! == 0)) then
      stack := stack.push c
    else
      reach := reach.set! j <| imports.foldl (init := j + 1) fun r c? =>
        match c? with
        | some c => max r (if reach[c]! == inProgress then never else reach[c]!)
        | none => never
      stack := stack.pop
  return (reach[i]!, { s with reach })

/-- Writes the index of the entries `entries` of the build of the workspace in `wsDir`. -/
private def write (wsDir : FilePath) (entries : Array Entry) (byName : Std.HashMap Name Nat) :
    IO FilePath := do
  let mut roots : Std.HashMap String Nat := {}
  let mut records := #[]
  for e in entries do
    let root := roots.getD e.root roots.size
    roots := roots.insert e.root root
    records := records.push {
      name := e.name, root, isModule := e.isModule
      imports := e.imports.map fun (imp, isLocal) =>
        let target := if !isLocal then noModule else
          match byName[imp.module]? with
          | some c => if c < entries.size then c else unknown
          | none => unknown
        { target, importAll := imp.importAll, isExported := imp.isExported, isMeta := imp.isMeta } }
  let rootNames := roots.fold (fun a r i => a.set! i r) (Array.replicate roots.size "")
  let bytes := encode rootNames records
  let dir ← buildDir wsDir
  IO.FS.createDirAll dir
  let file := dir / fileName bytes
  let tmp := file.addExtension "tmp"
  IO.FS.writeBinFile tmp bytes
  IO.FS.rename tmp file
  return file

/--
The index of this build of the workspace in `wsDir` that has the record of `mod` and its transitive
imports, written if no index has it yet, and the number of that record; `none` if no index can have
them, as a transitive import of `mod` has no entry, or if it cannot be written.
-/
public def indexFor (wsDir : FilePath) (mod : Module) : IO (Option (FilePath × Nat)) := do
  let promise : IO.Promise (Option FilePath) ← IO.Promise.new
  let r ← stateRef.modifyGet fun s =>
    let s := s.drain
    match s.byName[mod.name]? with
    | none => (none, s)
    | some i =>
      let (reach, s) := s.reachOf i
      if reach ≥ never then (none, s) else
      match s.written.find? (·.1 ≥ reach) with
      | some (_, p) => (some (i, p, none), s)
      | none =>
        (some (i, promise, some (s.entries, s.byName)),
          { s with written := s.written.push (s.entries.size, promise) })
  let some (i, p, toWrite?) := r | return none
  if let some (entries, byName) := toWrite? then
    p.resolve (← (write wsDir entries byName).toBaseIO).toOption
  return (← IO.wait p.result!).map (·, i)

/-- Ends a build of the workspace in `wsDir`: removes its indexes. -/
public def finish (wsDir : FilePath) : BaseIO Unit := do
  let s ← stateRef.swap {}
  if s.written.isEmpty || (← IO.getEnv "PAPERLEAN_SETUP_INDEX_KEEP").isSome then return
  discard <| (do IO.FS.removeDirAll (← buildDir wsDir) : IO Unit).toBaseIO

end Lake.PaperLean.SetupIndex
