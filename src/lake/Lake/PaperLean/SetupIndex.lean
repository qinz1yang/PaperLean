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
import Lake.Config.Monad
import Lake.PaperLean.SetupProviders
import Lake.PaperLean.BuiltinFacets
import Lake.PaperLean.Env
import Lean.PaperLean.System
import Std.Data.HashMap.Basic

/-!
Ordinary Lake writes the transitive artifact paths into every module setup.
PaperLean's additional setup files share a binary index per build. The standard
case uses one immutable v1 file. A preliminary source scan supplies only its
layout; a consumer can use a row only when the actual memoized input job and
every local import in its closure match. Selected export jobs supply path
overrides for artifacts outside their default location.

New or changed rows refer to the immutable records of their direct imports.
A module gets at most one such row in a run, even if library sources appear one
at a time. The writer never starts input jobs or waits for missing prerequisites.
Generation files survive through the last consumer and may be retained for tests.
-/

open System Lean
open Lean.PaperLean.SetupIndex (artifactsAt encode fileName noModule unknown RecordRef LinkedImport encodeLinked linkedFileName)

namespace Lake.PaperLean.SetupIndex

/-- A module whose header the build read. -/
structure Entry where
  name : Name
  owner : Name
  /-- The library directory of its package. -/
  root : String
  isModule : Bool
  /-- Its imports, and whether a package of the workspace has the module of each. -/
  imports : Array (Import × Bool)
  deriving Inhabited, BEq

private structure Base where
  file : FilePath
  hash : UInt64
  rows : Array Entry
  byName : Std.HashMap Name Nat

private inductive BaseStatus where
  | unplanned
  | unavailable
  | ready (base : Base)

private structure Writer where
  base : IO.Ref BaseStatus
  refs : IO.Ref (Std.HashMap Name RecordRef)

private initialize headerParser : IO.Ref (Option (String → Option (ModuleHeader × Nat))) ← IO.mkRef none

public def registerHeaderParser (parse : String → Option (ModuleHeader × Nat)) : BaseIO Unit :=
  headerParser.set (some parse)

structure State where
  /-- The build can infer its import graph and artifact locations from the builtin module facets. -/
  enabled : Bool := false
  owner? : Option Workspace := none
  /-- The exact registry owner for legacy context-free observations. -/
  buildContext? : Option BuildContext := none
  /-- A start and finish pair for each run, including two runs in the same workspace. -/
  runs : List FilePath := []
  generation : Nat := 0
  /-- A compiler requested a private launch file in this generation. -/
  launched : Bool := false
  /-- The directory of the first run. A later overlapping run cannot change its destination. -/
  outputDir : FilePath := ⟨""⟩
  /-- Deferred header producers, latest first. -/
  pending : List (Unit → Option Entry) := []
  entries : Array Entry := #[]
  byName : Std.HashMap Name Nat := {}
  writer? : Option Writer := none
  /-- Per-run writer queue, separate from the Lake store. No writer waits for a build job. -/
  tail? : Option (IO.Promise Unit) := none
  /-- The modules whose artifacts are not where the index has them. -/
  moved : NameSet := {}
  deriving Inhabited

private initialize standalone : IO.Ref State ← IO.mkRef {}
private initialize sessions : BuildSessions (IO.Ref State) ← BuildSessions.new


-- Legacy manual writers own the standalone session. Without one, legacy readers
-- can inspect a sole workspace run but cannot contribute facts to that run.
private def unscoped? : BaseIO (Option (IO.Ref State)) := do
  unless (← standalone.get).runs.isEmpty do return some standalone
  sessions.singleOr? (some standalone)

private def scoped? (ctx : BuildContext) : BaseIO (Option (IO.Ref State)) := do
  if let some ref ← sessions.find? ctx then return some ref
  if let some ref ← sessions.findRun? ctx then ref.modify fun s => { s with enabled := false }
  return none

/-- The directory of the indexes of the builds of the workspace in `wsDir`. -/
def indexesDir (wsDir : FilePath) : FilePath :=
  wsDir / ".lake" / "paperlean-setup"

private def enter (ref : IO.Ref State) (wsDir : FilePath) (eligible : Bool)
    (owner? : Option Workspace := none) : BaseIO Unit := do
  let writer? ← if eligible then
    pure <| some { base := ← IO.mkRef .unplanned, refs := ← IO.mkRef {} : Writer }
    else pure none
  let generation ← freshGeneration
  let pid ← IO.Process.getPID
  ref.modify fun s =>
    if s.runs.isEmpty then
      { enabled := eligible, owner?, writer?, runs := [wsDir], generation,
        outputDir := indexesDir wsDir / s!"{pid}-{generation}" }
    else
      { s with enabled := false, runs := wsDir :: s.runs }

private def cleanInterrupted (wsDir : FilePath) : BaseIO Unit := do
  let .ok entries ← (indexesDir wsDir).readDir.toBaseIO | return
  for d in entries do
    if let some pid := writerPid? d.fileName then
      unless ← Lean.PaperLean.processAlive pid do
        if let .ok md ← d.path.symlinkMetadata.toBaseIO then
          if md.type == .dir then discard <| (removePath d.path).toBaseIO

private def usesBuiltins (ws : Workspace) (builtins : FacetConfigMap) : Bool := Id.run do
  for facet in SetupProviders.facets do
    let some active := ws.facetConfigs.get? facet | return false
    let some builtin := builtins.get? facet | return false
    unless unsafe ptrEq active builtin do return false
  return true

public def startWithoutIndex (wsDir : FilePath) : BaseIO Unit := enter standalone wsDir false

public def start (wsDir : FilePath) : BaseIO Unit := do
  let active ← accelerated
  enter standalone wsDir active
  if active then cleanInterrupted wsDir

public def startForWorkspace (ws : Workspace) (builtins : FacetConfigMap) : BaseIO Unit := do
  let active ← accelerated
  enter standalone ws.dir (active && usesBuiltins ws builtins) (some ws)
  if active then cleanInterrupted ws.dir

private def isWorkspaceModule (ws : Workspace) (mod : Module) : Bool := Id.run do
  let some pkg := ws.packages[mod.pkg.wsIdx]? | return false
  unless unsafe ptrEq pkg mod.pkg do return false
  let some canonical := pkg.findModule? mod.name | return false
  return canonical.lib.name == mod.lib.name && (unsafe ptrAddrUnsafe canonical.lib.config == ptrAddrUnsafe mod.lib.config)

private def State.observeWorkspace (s : State) (ws : Workspace) : State :=
  if !s.enabled then s else
  match s.owner? with
  | some owner => if unsafe ptrEq owner ws then s else { s with enabled := false }
  | none => if s.runs == [ws.dir] then { s with owner? := some ws } else { s with enabled := false }

/-- Defers the header of `mod` until an index needs it, including its owner, library directory and
imports. The header is kept if imports of its name get it (`Workspace.findModule?`). -/
@[noinline, nospecialize] private def noteCore {α : Type} (ref : IO.Ref State)
    (ws : Workspace) (mod : Module) (isModule : Bool)
    (imports : Array α) (toImport : α → Import × Bool) : BaseIO Unit := do
  let entry : Unit → Option Entry := fun _ =>
    if (ws.findModule? mod.name).any (·.pkg.keyName == mod.pkg.keyName) then
      some { name := mod.name, owner := mod.pkg.keyName, root := mod.pkg.leanLibDir.toString, isModule,
             imports := imports.map toImport }
    else none
  ref.modify fun s =>
    let s := s.observeWorkspace ws
    if s.enabled && s.runs == [ws.dir] then { s with pending := entry :: s.pending } else s

public def note {α : Type} (ws : Workspace) (mod : Module) (isModule : Bool)
    (imports : Array α) (toImport : α → Import × Bool) : BaseIO Unit := do
  noteCore standalone ws mod isModule imports toImport

/-- Notes the files of `mod` that `Module.computeExportInfo` gives its importers, its `.olean`
parts and its IR files, if they are not where the index has them, by `note` with `isModule`. -/
private def noteArtifactsCore (ref : IO.Ref State) (mod : Module) (isModule : Bool) (files : Array FilePath) :
    BaseIO Unit := do
  let generation? ← (fun s => if s.enabled then some s.generation else none) <$> ref.get
  let some generation := generation? | return
  let atDefault := artifactsAt mod.pkg.leanLibDir mod.name isModule true
  unless files.map toString == atDefault.toArrays.flatten.map toString do
    ref.modify fun s =>
      if s.enabled && s.generation == generation then { s with moved := s.moved.insert mod.name } else s

public def noteArtifacts (mod : Module) (isModule : Bool) (files : Array FilePath) : BaseIO Unit := do
  noteArtifactsCore standalone mod isModule files

/-- A run owns its recorded headers and immutable generation through its last job. -/
public def beginRun (ctx : BuildContext) (ws : Workspace) (enabled : Bool) : BaseIO Unit := do
  let active := enabled && !ctx.noBuild && (← accelerated)
  let eligible := active && (← builtinFacetMap.get).any (usesBuiltins ws)
  let ref ← IO.mkRef {}
  enter ref ws.dir eligible (some ws)
  if eligible then ref.modify fun s => {s with buildContext? := some ctx}
  sessions.insert ctx ref
  SetupProviders.beginRun ctx eligible (isWorkspaceModule ws) {
    input := fun mod input => noteCore ref ws mod input.header.isModule input.imports fun imp =>
      (imp.toImport, imp.module?.isSome)
    exports := fun mod info => do
      let isModule := info.allArts.oleanServer?.isSome
      let defaultView := artifactsAt mod.pkg.leanLibDir mod.name isModule
      if info.arts.toArrays != (defaultView false).toArrays ||
          info.allArts.toArrays != (defaultView true).toArrays then
        ref.modify fun s => if s.enabled then {s with moved := s.moved.insert mod.name} else s
  }
  if active then cleanInterrupted ws.dir

/-- Whether this run tracks provider results for compiling a shared setup. -/
public def observesProviders (ctx : BuildContext) : BaseIO Bool := SetupProviders.observing ctx

private def readMoves (ref : IO.Ref State) : BaseIO NameSet := do
  if let some ctx := (← ref.get).buildContext? then SetupProviders.observeExports ctx
  return (← ref.get).moved

public def moved : BaseIO NameSet := do
  if let some ref ← unscoped? then return ← readMoves ref
  return {}

public def movedFor (ctx : BuildContext) : BaseIO NameSet := do
  if let some ref ← scoped? ctx then return ← readMoves ref
  return {}

/-- A successful indexed compile already inspected every export in its closure. -/
public def indexedMoves (ctx : BuildContext) : BaseIO NameSet := do
  if let some ref ← scoped? ctx then return (← ref.get).moved
  return {}

/-- Adds the pending headers in the order noted, keeping the first of each name. The shared state
buffers them so a build that compiles nothing does not copy the index's arrays for every header. -/
private def State.drain (s : State) : State := Id.run do
  if s.pending.isEmpty then return s
  let pending := s.pending.reverse
  let mut entries := s.entries
  let mut byName := s.byName
  let s := { s with pending := [], entries := #[], byName := {} }
  for makeEntry in pending do
    let some entry := makeEntry () | continue
    unless byName.contains entry.name do
      let i := entries.size
      entries := entries.push entry
      byName := byName.insert entry.name i
  return {s with entries, byName}

-- Write the complete contents under a temporary sibling before linking its final
-- name. An existing content-addressed file must contain precisely the same bytes.
private def publishBytes (file : FilePath) (bytes : ByteArray) : IO Unit := do
  let tmp := file.addExtension s!"tmp-{← freshGeneration}"
  let h ← IO.FS.Handle.mk tmp .writeNew
  let publish : IO Unit := do
    h.write bytes
    h.flush
    unless System.Platform.isWindows do IO.setAccessRights tmp { user := {read := true}, group := {read := true}, other := {read := true} }
    try
      IO.FS.hardLink tmp file
    catch e =>
      unless (e matches .alreadyExists ..) do throw e
      let some (size, existing) ← Lean.PaperLean.SetupIndex.readRegularPrefix file.toString bytes.size.toUSize
        | throw <| IO.userError "cannot verify an existing setup index file"
      unless size.toNat == bytes.size && existing.data == bytes.data do
        throw <| IO.userError "setup index content hash collision"
  try publish
  finally
    discard <| (IO.FS.removeFile tmp).toBaseIO

-- Both index formats serialize string components and lengths as little-endian
-- UInt32s. Never turn an unsupported module name into a different artifact path.
private def nameBytes? (name : Name) : Option Nat := do
  if name.isAnonymous then return ← none
  go name 0 4
where
  go : Name → Nat → Nat → Option Nat
    | .anonymous, _, total => some total
    | .num .., _, _ => none
    | .str pre part, count, total =>
      if part.isEmpty || part == "." || part == ".." || part.contains '/' ||
          part.contains '\\' || part.contains (Char.ofNat 0) ||
          part.utf8ByteSize ≥ UInt32.size || count + 1 ≥ UInt32.size then none
      else go pre (count + 1) (total + 4 + part.utf8ByteSize)

private def rowBytes? (row : Entry) : Option Nat := do
  let name ← nameBytes? row.name
  guard <| !row.root.isEmpty && !row.root.contains (Char.ofNat 0) &&
    row.root.utf8ByteSize < UInt32.size && row.imports.size < UInt32.size
  for (imp, _) in row.imports do discard <| nameBytes? imp.module
  return name + 9 + 5 * row.imports.size

/-- Encode the fast v1 layout once. A row is never trusted just because it is in
this file; `resolve` separately proves that its selected closure agrees. -/
private def publishBase (dir : FilePath) (rows : Array Entry) (byName : Std.HashMap Name Nat) :
    IO Base := do
  let mut roots : Std.HashMap String Nat := {}
  let mut records := #[]
  for e in rows do
    let root := roots.getD e.root roots.size
    roots := roots.insert e.root root
    records := records.push {
      name := e.name, root, isModule := e.isModule
      imports := e.imports.map fun (imp, isLocal) =>
        let target := if isLocal then byName.getD imp.module unknown else noModule
        { target, importAll := imp.importAll, isExported := imp.isExported, isMeta := imp.isMeta } }
  let rootNames := roots.fold (fun a r i => a.set! i r) (Array.replicate roots.size "")
  let bytes := encode rootNames records
  let file := dir / fileName bytes
  unless ← Lean.PaperLean.SetupIndex.publish file.toString bytes do publishBytes file bytes
  return { hash := bytes.hash, file, rows, byName }

-- Planning is optional. These limits bound extra work even if incomplete or
-- changing source files temporarily describe a much larger graph.
private def maxProbes := 65536
private def totalPrefixBudget := 128 * 1024 * 1024
private def maxPrefix := 1024 * 1024

private def provisional (ws : Workspace) (mod : Module) (parse : String → Option (ModuleHeader × Nat))
    (budget : Nat) : IO (Option Entry × Nat) := do
  let mut used := 0
  let mut request := 4096
  while used < budget do
    let limit := min (budget - used) request
    -- Charge requests, including rejected or unreadable paths. Actual I/O
    -- never exceeds these limits. Unsupported systems use selected inputs.
    used := used + limit
    let .ok (some (fileSize, bytes)) ←
        (Lean.PaperLean.SetupIndex.readRegularPrefix mod.leanFile.toString limit.toUSize).toBaseIO
      | return (none, used)
    let full := fileSize.toNat == bytes.size
    if let some source := String.fromUTF8? bytes then
      if let some (header, consumed) := parse source then
        -- Enough bytes follow the parser's first non-header token. If a
        -- prefix ended inside a token, retry it or leave the row unplanned.
        if full || consumed + 32 < bytes.size then
          return (some {
            name := mod.name, owner := mod.pkg.keyName, root := mod.pkg.leanLibDir.toString
            isModule := header.isModule
            imports := header.imports.map fun imp => (imp, (ws.findModule? imp.module).isSome) }, used)
    if full || request ≥ maxPrefix then break
    request := min (2 * request) maxPrefix
  return (none, used)

private def computeBase (dir : FilePath) (ws : Workspace) (selected : Array Entry)
    (seeds : Array Name) : IO Base := do
  let mut rows := #[]
  let mut byName : Std.HashMap Name Nat := {}
  let mut todo := seeds
  -- Overestimate by charging each row's root separately. All record offsets
  -- and root/record counts must fit the v1 encoding (including its sentinels).
  let mut bytes := Lean.PaperLean.SetupIndex.magic.utf8ByteSize + 8
  for row in selected do
    let some b := rowBytes? row | continue
    let n := bytes + 4 + b + 4 + row.root.utf8ByteSize
    if n ≥ UInt32.size || rows.size ≥ unknown then continue
    bytes := n
    byName := byName.insert row.name rows.size
    rows := rows.push row
    for (imp, localImp) in row.imports do
      if localImp then todo := todo.push imp.module
  if let some parse ← headerParser.get then
    let mut seen := ({} : NameSet)
    let mut remaining := totalPrefixBudget
    let mut attempts := 0
    while let some name := todo.back? do
      todo := todo.pop
      if byName.contains name || seen.contains name then continue
      if attempts ≥ maxProbes || remaining == 0 then break
      seen := seen.insert name
      unless (nameBytes? name).isSome do continue
      let some mod := ws.findModule? name | continue
      attempts := attempts + 1
      let (row?, charged) ← provisional ws mod parse remaining
      remaining := remaining - charged
      let some row := row? | continue
      let some b := rowBytes? row | continue
      let n := bytes + 4 + b + 4 + row.root.utf8ByteSize
      if n ≥ UInt32.size || rows.size ≥ unknown then break
      bytes := n
      byName := byName.insert name rows.size
      rows := rows.push row
      for (imp, localImp) in row.imports do
        if localImp then todo := todo.push imp.module
  return ← publishBase dir rows byName

private def commitRow (writer : Writer) (dir : FilePath) (base : Base) (row : Entry) :
    IO RecordRef := do
  unless (rowBytes? row).isSome do throw <| IO.userError "unsupported setup index record"
  let refs ← writer.refs.get
  let mut agrees := base.byName[row.name]?.any fun i => base.rows[i]! == row
  let mut imports : Array LinkedImport := #[]
  for (imp, localImp) in row.imports do
    let target := if localImp then refs[imp.module]? else none
    if localImp then
      let some ref := target | throw <| IO.userError "missing selected import"
      let same := match ref with
        | .base hash id => hash == base.hash && base.byName[imp.module]? == some id
        | .node _ => false
      unless same do agrees := false
    imports := imports.push {
      module := imp.module, target, importAll := imp.importAll
      isExported := imp.isExported, isMeta := imp.isMeta }
  if agrees then return .base base.hash (base.byName.getD row.name 0)
  let bytes := encodeLinked {name := row.name, root := row.root, isModule := row.isModule, imports}
  let hash := bytes.hash
  publishBytes (dir / linkedFileName hash) bytes
  return .node hash

/-- Certify the actual graph bottom-up. The accepted canonical job for a name is
unique in a run. Its resulting reference is shared by all parents. An ordinary
matching row stays in the mapped base. Each other row is published exactly once
with direct edges to previously certified records. -/
private def resolve (writer : Writer) (dir : FilePath) (base : Base) (rows : Array Entry)
    (byName : Std.HashMap Name Nat) (root : Nat) : IO (Option RecordRef) := do
  let mut stack := #[(root, 0)]
  let mut active : Std.HashSet Nat := {}
  active := active.insert root
  while h : 0 < stack.size do
    let (i, next) := stack.back
    let row := rows[i]!
    if (← writer.refs.get).contains row.name then
      stack := stack.pop
      active := active.erase i
    else if next == row.imports.size then
      let result ← commitRow writer dir base row
      writer.refs.modify (·.insert row.name result)
      active := active.erase i
      stack := stack.pop
    else
      let (imp, localImp) := row.imports[next]!
      stack := stack.set! (stack.size - 1) (i, next + 1)
      if localImp && !(← writer.refs.get).contains imp.module then
        let some j := byName[imp.module]? | return none
        if active.contains j then return none
        active := active.insert j
        stack := stack.push (j, 0)
  return (← writer.refs.get)[rows[root]!.name]?

private def indexForCore (ref : IO.Ref State) (wsDir : FilePath) (mod : Module)
    (getSeeds : BaseIO (Array Name)) : IO (Option (FilePath × Nat)) := do
  let done : IO.Promise Unit ← IO.Promise.new
  let ready ← ref.modifyGet fun s =>
    if !s.enabled || s.runs != [wsDir] then (none, s) else
    match s.writer?, s.owner? with
    | some writer, some ws =>
      (some (writer, ws, s.outputDir, s.tail?), {s with tail? := some done})
    | _, _ => (none, s)
  let some (writer, ws, dir, before?) := ready | return none
  try
    if let some prev := before? then discard <| IO.wait prev.result?
    let selected ← ref.modifyGet fun s =>
      if !s.enabled || s.outputDir != dir then (none, s) else
      let s := s.drain
      (s.byName[mod.name]?.bind (fun i =>
        if s.entries[i]!.owner == mod.pkg.keyName then some (i, s.entries, s.byName) else none), s)
    let some (i, entries, byName) := selected | return none
    let base ← match ← writer.base.get with
      | .ready base => pure base
      | .unavailable => return none
      | .unplanned => do
        -- A failed or interrupted plan cannot rescan the workspace at each compile.
        writer.base.set .unavailable
        IO.FS.createDirAll dir
        let base ← computeBase dir ws entries (← getSeeds)
        writer.base.set (.ready base)
        pure base
    let some loc ← resolve writer dir base entries byName i | return none
    return some <| match loc with
      | .base _ id => (base.file, id)
      | .node hash => (dir / linkedFileName hash, 0)
  catch _ => return none
  finally done.resolve ()

public def indexFor (wsDir : FilePath) (mod : Module) : IO (Option (FilePath × Nat)) := do
  let some ref ← unscoped? | return none
  if let some ctx := (← ref.get).buildContext? then
    unless ← SetupProviders.prepareStored ctx mod do return none
  indexForCore ref wsDir mod (pure #[])

/-- Check the consumer’s real store and dispatcher before omitting transitive lookups. -/
public def indexForModule (ws : Workspace) (mod : Module) : FetchM (Option (FilePath × Nat)) :=
  .mk fun fetch _ _ store ctx => do
    let some ref ← scoped? ctx | return none
    unless ← SetupProviders.mayIndex ctx store fetch mod do return none
    indexForCore ref ws.dir mod (SetupProviders.activeModules ctx)

/-- Allocate private compiler setup files in the generation that owns their jobs. -/
public def launchDirFor (ctx : BuildContext) : BaseIO (Option FilePath) := do
  let some ref ← sessions.find? ctx | return none
  ref.modifyGet fun s =>
    if s.runs.isEmpty then (none, s) else (some s.outputDir, { s with launched := true })


private def finishCore (ref : IO.Ref State) (wsDir : FilePath) : BaseIO Unit := do
  let old ← ref.modifyGet fun s =>
    if !s.runs.contains wsDir then (none, s) else
    let runs := s.runs.erase wsDir
    if runs.isEmpty then
      (some (s.outputDir, s.tail?, s.writer?, s.launched), { generation := s.generation })
    else
      (none, { s with runs })
  let some (dir, tail?, writer?, launched) := old | return
  if let some tail := tail? then discard <| IO.wait tail.result?
  let published ← match writer? with
    | some writer => pure ((← writer.base.get) matches .ready _)
    | none => pure false
  if published then
    if (← IO.getEnv "PAPERLEAN_SETUP_INDEX_KEEP").isNone then
      discard <| (removePath dir).toBaseIO
  else if launched || tail?.isSome then
    discard <| (IO.FS.removeDir dir).toBaseIO

public def finish (wsDir : FilePath) : BaseIO Unit := finishCore standalone wsDir

public def endRun (ctx : BuildContext) : BaseIO Unit := do
  SetupProviders.endRun ctx
  if let some ref ← sessions.take? ctx then
    if let wsDir :: _ := (← ref.get).runs then finishCore ref wsDir

end Lake.PaperLean.SetupIndex
