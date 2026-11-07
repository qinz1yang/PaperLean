/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lake.Config.Module
public import Lake.Config.Workspace
import Lake.Config.Env
import Lake.PaperLean.Env
import Lake.PaperLean.BuildEnv
public import Lake.PaperLean.BuildSessions
import Lake.PaperLean.Cache
import Lean.PaperLean.OLeanPack
import Lean.PaperLean.System
import Lean.Data.NameMap.Basic

/-!
Olean packs written during a build, for the `lean` processes that the build starts later. When Lake
runs for a `paperlean` command (`Lake.PaperLean.accelerated`), the workspace has no prepared data
(`Lake.PaperLean.Env`) and a build has compiled `minModules` modules, Lake packs the modules that the
build compiles, in batches as they finish (`moduleDone`),
and uses a pack of the toolchain's library, which it writes once into PaperLean's cache directory
(`Cache.root?`; `toolchainPack`) and again only when the library changed, and which prepared data uses
too. Every `lean`
that the build starts afterwards reads its imports from the packs written so far
(`Lake.PaperLean.BuildEnv`, `LEAN_OLEAN_PACK`). A pack only changes how files are read, so what a
module compiles to does not depend on which packs exist when it starts. (No import image is
written: an image of the toolchain's library alone makes the import of states with many entries of
other modules slower, as those are then replayed instead of folded.) The build's own packs are in
`.lake/paperlean/build/<process id>-<generation>/` and are removed at the end of the build (`finish`), or, if it
was interrupted, by the next `paperlean build` or `paperlean prepare` (`removeEnded`).
`PAPERLEAN_BUILD_PACKS=0` turns this off, `PAPERLEAN_BUILD_PACKS=1` packs from the first compiled
module on.
-/

open System Lean

namespace Lake.PaperLean.BuildData

/-- The packs of this build. -/
structure State where
  /-- The workspace's directory. -/
  wsDir : FilePath
  dir : FilePath
  /-- Each finished module not packed yet: its library directory and its chains of files. -/
  pending : Array (String × Array (Array String)) := #[]
  /-- When the oldest pending module finished (ms). -/
  pendingSince : Nat := 0
  /-- The number of modules packed or being packed. -/
  packed : Nat := 0
  /-- Whether a pack is being written. -/
  writing : Bool := false
  /-- The number of packs started, which gives the next pack's address. -/
  started : Nat := 0
  /-- The number of modules per pack, if fixed (`PAPERLEAN_BUILD_PACK_BATCH`, for tests). -/
  batch? : Option Nat := none

private inductive Packing where
  | waiting (early : Array (String × Array (Array String)))
  | disabled
  | active (data : State)

private structure Activity where
  count : Nat := 0
  closing? : Option (IO.Promise Unit) := none
  deriving Inhabited

private structure Session where
  generation : Nat
  enabled : Bool
  workspace? : Option FilePath
  state : IO.Ref Packing
  initializing : BuildMutex Unit
  compiled : IO.Ref NameSet
  activity : IO.Ref Activity
  lock : IO.Ref (Option IO.FS.Handle)
  packs : BuildEnv.PackList

private initialize runs : BuildSessions Session ← BuildSessions.new
private initialize standalone : BuildMutex (Option Session) ← BuildMutex.new none

private def newSession (packs : BuildEnv.PackList) (enabled : Bool) (ws? : Option FilePath) :
    BaseIO Session := do
  return {
    generation := ← freshGeneration
    enabled, workspace? := ws?
    state := ← IO.mkRef (.waiting #[])
    initializing := ← BuildMutex.new ()
    compiled := ← IO.mkRef {}
    activity := ← IO.mkRef {}
    lock := ← IO.mkRef none
    packs
  }

private def standaloneOrRun? : BaseIO (Option Session) := do
  let session ← standalone.atomically do
    if let some s ← get then return s
    let s ← newSession (← BuildEnv.standalonePacks) true none
    set (some s)
    return s
  runs.singleOr? (some session)

public def startFor (ctx : BuildContext) (wsDir : FilePath) (enabled : Bool) : BaseIO Unit := do
  let enabled := enabled && (← accelerated)
  runs.insert ctx (← newSession (← BuildEnv.enter enabled) enabled (some wsDir))

/-- Compiler environment for the build that owns `ctx` and its workspace. -/
public def leanEnvFor (ctx : BuildContext) : BaseIO (Array (String × Option String)) := do
  let s? ← runs.find? ctx
  BuildEnv.makeEnv (s?.bind fun s => if s.enabled then some s.packs else none)

-- Retirement excludes new work and waits for operations and writers already admitted.
private def enter (s : Session) : BaseIO Bool := do
  unless s.enabled do return false
  s.activity.modifyGet fun state =>
    if state.closing?.isSome then (false, state)
    else (true, {state with count := state.count + 1})

private def leave (s : Session) : BaseIO Unit := do
  let ready ← s.activity.modifyGet fun state =>
    let remaining := state.count - 1
    (if remaining == 0 then state.closing? else none, {state with count := remaining})
  if let some promise := ready then promise.resolve ()

private def inSession (s : Session) (f : IO Unit) : IO Unit := do
  unless ← enter s do return
  try f finally leave s

private def background (s : Session) (f : IO Unit) : BaseIO Unit := do
  unless ← enter s do return
  discard <| BaseIO.asTask (prio := .dedicated) do
    try discard f.toBaseIO finally leave s

/-- A build packs once it has compiled this many modules: a smaller build would not profit. -/
private def minModules : Nat := 32

/-- The address of the `i`-th pack of a build: 64 GiB apart, above those of prepared data. -/
private def baseAddr (i : Nat) : USize :=
  0x300000000000 + (i * 0x1000000000).toUSize

/-- The address of the pack of the toolchain's library. -/
private def toolchainBaseAddr : USize := 0x2c0000000000

/-- The minimum number of finished modules in a pack: packs grow with the number of modules packed,
so that a build of many modules writes a few dozen packs. -/
private def minBatch (s : State) : Nat :=
  s.batch?.getD (max 64 (s.packed / 4))

/-- How long a finished module waits for its batch (ms): longer the more packs the build wrote, as
every later `lean` of the build maps all of them. -/
private def maxWait (s : State) : Nat := 20000 * (1 + s.started / 8)

/-- The number of packs that a build writes at most (a process serves modules from 255 packs). -/
private def maxPacks : Nat := 128

/-- The files below `dir` as packs chain them: each module's `.olean` parts, and its IR files. -/
private def chainsBelow (dir : FilePath) : IO (Array (Array String)) := do
  let mut chains := #[]
  for p in ← dir.walkDir do
    let f := p.toString
    if f.endsWith ".olean" then
      let mut chain := #[f]
      if ← FilePath.pathExists (f ++ ".server") then
        chain := chain.push (f ++ ".server")
        if ← FilePath.pathExists (f ++ ".private") then
          chain := chain.push (f ++ ".private")
      chains := chains.push chain
    else if f.endsWith ".ir.sig" then
      let ir := (f.dropEnd 4).toString
      chains := chains.push (if ← FilePath.pathExists ir then #[f, ir] else #[f])
  return chains

/-- The files of `mod` as packs chain them. -/
private def chainsOf (mod : Module) : IO (Array (Array String)) := do
  let some olean ← existing mod.oleanFile | return #[]
  let mut chain := #[olean]
  if let some server ← existing mod.oleanServerFile then
    chain := chain.push server
    if let some priv ← existing mod.oleanPrivateFile then
      chain := chain.push priv
  let mut chains := #[chain]
  if let some sig ← existing mod.irSigFile then
    chains := chains.push (match ← existing mod.irFile with | some ir => #[sig, ir] | none => #[sig])
  return chains
where
  existing (f : FilePath) : IO (Option String) := do
    return if ← f.pathExists then some f.toString else none

/-- `dir` without trailing separators, as packs record their roots. -/
private def rootString (dir : FilePath) : String :=
  (dir.toString.dropEndWhile (· == '/')).toString

/-- A stamp of the files of `chains`: their names, sizes and modification times; and their total
size. -/
private def stamp (chains : Array (Array String)) : IO (UInt64 × Nat) := do
  let mut h : UInt64 := 11
  let mut size := 0
  for chain in chains do
    for f in chain do
      let m ← FilePath.metadata f
      h := mixHash h (hash f)
      h := mixHash h m.byteSize
      h := mixHash h (hash m.modified.sec)
      h := mixHash h m.modified.nsec.toUInt64
      size := size + m.byteSize.toNat
  return (h, size)

/-- The number of packs of other toolchains (or of earlier states of a toolchain) kept. -/
private def keptToolchainPacks : Nat := 2

/-- Removes a pack's directory entry and its identity file, leaving directories untouched. -/
public def removePack (pack : FilePath) : IO Unit := do
  for path in #[pack, FilePath.mk (Lean.PaperLean.OLeanPack.identityFile pack.toString)] do
    try IO.FS.removeFile path catch
      | .noFileOrDirectory .. => pure ()
      | err => throw err

/-- Removes from `dir` the temporary files of writers that ended before renaming theirs (`.tmp.<pid>-<generation>`, `.tmp.<pid>`,
also after an earlier `.tmp-<pid>`), and the packs other than `current` beyond the
`keptToolchainPacks` newest if no build uses them. -/
private def cleanToolchainPacks (dir current : FilePath) : IO Unit := do
  let mut others := #[]
  for d in ← dir.readDir do
    let f := d.fileName
    let tempPid? (sep : String) : Option UInt32 := match f.split sep |>.toStringList with
      | [] | [_] => none
      | parts => parts.getLast?.bind writerPid?
    if let some pid := tempPid? ".tmp." <|> tempPid? ".tmp-" then
      unless ← Lean.PaperLean.processAlive pid do
        try IO.FS.removeFile d.path catch _ => pure ()
    else if f.endsWith ".paperlean" && !f.startsWith "id-" && d.path != current then
      try others := others.push (d.path, (← d.path.metadata).modified) catch _ => pure ()
  for (pack, _) in (others.qsort fun a b => compare a.2 b.2 == .gt)[keptToolchainPacks:] do
    try
      let some h ← Lean.PaperLean.OLeanPack.openRegularForLock pack.toString | do
        removePack pack
        continue
      if ← h.tryLock (exclusive := true) then
        removePack pack
        h.unlock
    catch _ => pure ()

/--
The pack of the toolchain's library `leanLibDir` in PaperLean's cache directory `cache`, relative to
it, if there is or can be one. Its name holds a stamp of the library's files and PaperLean's version
and build, so that a pack is only used for the library as it was packed, by the build that packed it.
Its writer renames it into place once it is on the disk, so that concurrent builds and later ones see
a whole pack, and locks it until its identity is recorded, which they wait for at their shared lock. One
that cannot be read, or some of whose files changed since it was written (a toolchain installed again
keeps their names, sizes and modification times), is written again, unless another build uses it:
then this one does too, as every packed file is checked before it is served. It is not written without
the disk space for it (and a tenth more). With `keep`, the shared lock stays held until the build
ends (`finish`), so that no other build removes the pack meanwhile.
-/
private def toolchainPackCore (cache leanLibDir : FilePath) (lock? : Option (IO.Ref (Option IO.FS.Handle))) : IO (Option String) := do
  let root := rootString leanLibDir
  let chains := (← chainsBelow leanLibDir).qsort fun a b => a[0]! < b[0]!
  if chains.isEmpty then return none
  let dir := cache / "toolchain-packs"
  let (h, size) ← stamp chains
  let stampHex := String.ofList (Nat.toDigits 16 h.toNat)
  let name := s!"lib-{hash root}-{stampHex}-{Lean.PaperLean.version}+{Lean.PaperLean.build}"
  let pack := dir / s!"{name}.paperlean"
  let rel := s!"toolchain-packs/{name}.paperlean"
  Cache.ensureRoot cache
  IO.FS.createDirAll dir
  cleanToolchainPacks dir pack
  let use (h : IO.FS.Handle) : IO (Option String) := do
    if let some lock := lock? then lock.set (some h) else h.unlock
    return some rel
  for _ in [0:2] do
    unless ← pack.pathExists do
      if size + size / 10 > (← availableSpace dir) then return none
      discard <| Lean.PaperLean.OLeanPack.createOf chains #[root] pack toolchainBaseAddr
    let some h ← Lean.PaperLean.OLeanPack.openRegularForLock pack.toString | do
      if ← pack.isDir then return none
      if size + size / 10 > (← availableSpace dir) then return none
      discard <| Lean.PaperLean.OLeanPack.createOf chains #[root] pack toolchainBaseAddr
      continue
    h.lock (exclusive := false)
    -- unless another build removed it before this one held the lock
    if ← pack.pathExists then
      if ← usable pack then return ← use h
      unless ← h.tryLock (exclusive := true) do
        -- (a failed conversion of the lock may have released it, and another build may have removed
        -- the pack meanwhile)
        h.lock (exclusive := false)
        if ← pack.pathExists then return ← use h
        h.unlock
        continue
      removePack pack
      h.unlock
  return none
where
  usable (pack : FilePath) : IO Bool := do
    try
      let (stale, _) ← Lean.PaperLean.OLeanPack.staleness pack.toString
      return stale == 0
    catch _ => return false

-- The native writer uses the PID in its temporary filename. An explicit prepare
-- can request the same toolchain pack as a build in this process.
private initialize toolchainMutex : BuildMutex Unit ← BuildMutex.new ()

private def writeToolchain (cache leanLibDir : FilePath) (lock? : Option (IO.Ref (Option IO.FS.Handle))) :
    IO (Option String) := toolchainMutex.atomically do
  toolchainPackCore cache leanLibDir lock?

public def toolchainPack (cache leanLibDir : FilePath) (keep : Bool) : IO (Option String) := do
  unless keep do return ← writeToolchain cache leanLibDir none
  let some s ← standaloneOrRun? | return none
  unless ← enter s do return none
  try writeToolchain cache leanLibDir (some s.lock) finally leave s

/-- Writes the pack `i` of `batch` in the background, then records it. -/
private def writePack (session : Session) (dir : FilePath) (i : Nat) (batch : Array (String × Array (Array String))) :
    BaseIO Unit := do
  background session do
    let out := dir / s!"pack-{i}.paperlean"
    let roots := batch.foldl (init := #[]) fun rs (r, _) => if rs.contains r then rs else rs.push r
    try
      -- deleted at the end of the build, or by the next one if this one did not end
      discard <| Lean.PaperLean.OLeanPack.createOf (batch.flatMap (·.2)) roots out (baseAddr i) (sync := false)
      session.packs.modify (·.push out.toString)
    catch _ => pure ()
    session.state.modify fun
      | .active s => .active { s with writing := false }
      | st => st

/-- Starts writing a pack of the pending modules if they are enough or have waited long enough. -/
private def maybeWrite (session : Session) : BaseIO Unit := do
  let now ← IO.monoMsNow
  let job? ← session.state.modifyGet fun
    | .active s =>
      if s.started ≥ maxPacks then
        (none, .active { s with pending := #[] })
      else if s.writing || s.pending.isEmpty ||
          (s.pending.size < minBatch s && now - s.pendingSince < maxWait s) then
        (none, .active s)
      else
        (some (s.dir, s.started, s.pending),
           .active { s with pending := #[], packed := s.packed + s.pending.size, writing := true,
                              started := s.started + 1 })
    | st => (none, st)
  if let some (dir, i, batch) := job? then
    writePack session dir i batch

/-- Removes the packs of the builds of the workspace in `wsDir` whose process ended without removing
them (interrupted ones). -/
public def removeEnded (wsDir : FilePath) : BaseIO Unit := do
  let .ok entries ← (dataDir wsDir / "build").readDir.toBaseIO | return
  for d in entries do
    if let some pid := writerPid? d.fileName then
      unless ← Lean.PaperLean.processAlive pid do
        discard <| (removePath d.path).toBaseIO

/-- Decides whether this build packs, and if so, starts using the toolchain's pack (in the
background) and packs the modules compiled so far. -/
private def start (session : Session) (wsDir leanLibDir : FilePath) : IO Unit := session.initializing.atomically do
  unless (← session.state.get) matches .waiting _ do return
  let disabled := !(← accelerated) || (← IO.getEnv "PAPERLEAN_BUILD_PACKS") == some "0" ||
    (← IO.getEnv dataMarker).isSome || (← explicitDataVars)
  let state? ← if disabled then pure none else do
    removeEnded wsDir
    let name := s!"{← IO.Process.getPID}-{session.generation}"
    let dir := dataDir wsDir / "build" / name
    let batch? := (← IO.getEnv "PAPERLEAN_BUILD_PACK_BATCH").bind (·.toNat?)
    try
      IO.FS.createDirAll dir
      pure (some ({ wsDir, dir, batch? } : State))
    catch _ => pure none
  let some data := state? | session.state.set .disabled
  let now ← IO.monoMsNow
  session.state.modify fun
    | .waiting early => .active { data with pending := early, pendingSince := now }
    | st => st
  background session do
    let some cache ← Cache.root? | return
    if let some pack ← writeToolchain cache leanLibDir (some session.lock) then
      session.packs.modify (·.push (cache / pack).toString)
  maybeWrite session

/-- Called before the build compiles the module `mod` of the workspace in `wsDir`, whose toolchain's
library is `leanLibDir`: starts packing once the build has compiled enough modules. -/
private def compileStartingIn (session : Session) (mod : Module) (wsDir leanLibDir : FilePath) : IO Unit := do
  if session.workspace?.any (· != wsDir) then return
  let n ← session.compiled.modifyGet fun s => let s := s.insert mod.name; (s.size, s)
  match ← session.state.get with
  | .active _ => maybeWrite session
  | .disabled => return
  | .waiting _ =>
    if n ≥ minModules || (← IO.getEnv "PAPERLEAN_BUILD_PACKS") == some "1" then
      start session wsDir leanLibDir

/-- Called when the build is done with `mod` (its files are final): packs it with the next batch if
the build compiled it. -/
private def moduleDoneIn (session : Session) (mod : Module) : IO Unit := do
  unless session.enabled do return
  unless (← session.compiled.get).contains mod.name do return
  inSession session do
    if (← session.state.get) matches .disabled then return
    let chains ← chainsOf mod
    if chains.isEmpty then return
    let entry := (rootString mod.pkg.leanLibDir, chains)
    let now ← IO.monoMsNow
    let active ← session.state.modifyGet fun
      | .waiting early => (false, .waiting (early.push entry))
      | .active s =>
        let pendingSince := if s.pending.isEmpty then now else s.pendingSince
        (true, .active { s with pending := s.pending.push entry, pendingSince })
      | .disabled => (false, .disabled)
    if active then maybeWrite session

public def compileStartingFor (ctx : BuildContext) (mod : Module) (wsDir leanLibDir : FilePath) :
    IO Unit := do
  if let some s ← runs.find? ctx then inSession s (compileStartingIn s mod wsDir leanLibDir)

public def moduleDoneFor (ctx : BuildContext) (mod : Module) : IO Unit := do
  if let some s ← runs.find? ctx then moduleDoneIn s mod

public def compileStarting (mod : Module) (wsDir leanLibDir : FilePath) : IO Unit := do
  if let some s ← standaloneOrRun? then inSession s (compileStartingIn s mod wsDir leanLibDir)

public def moduleDone (mod : Module) : IO Unit := do
  if let some s ← standaloneOrRun? then moduleDoneIn s mod

/-- Retire this run's writers before releasing the lock and deleting its pack directory. -/
private def finishSession (s : Session) : BaseIO Unit := do
  let promise ← IO.Promise.new
  let (wait, closing) ← s.activity.modifyGet fun state =>
    let closing := state.closing?.getD promise
    ((state.count != 0, closing), {state with closing? := some closing})
  if wait then discard <| IO.wait closing.result?
  s.packs.set #[]
  s.lock.set none
  if let .active data ← s.state.swap .disabled then
    if (← IO.getEnv "PAPERLEAN_BUILD_PACKS_KEEP").isNone then
      discard <| (removePath data.dir).toBaseIO

public def finishFor (ctx : BuildContext) : BaseIO Unit := do
  if let some s ← runs.findRun? ctx then
    finishSession s
    BuildEnv.leave s.packs
  discard <| runs.take? ctx

/-- Finish the standalone packing session. Workspace runs retire their own session. -/
public def finish : BaseIO Unit := do
  let previous ← standalone.atomically do
    BuildEnv.renewStandalone
    modifyGet fun s => (s, none)
  if let some s := previous then finishSession s

end Lake.PaperLean.BuildData
