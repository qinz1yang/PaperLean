/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
import Init
public import Lake.Config.Module
public import Lake.Config.Workspace
import Lake.Config.Env
import Lake.PaperLean.Env
import Lake.PaperLean.BuildEnv
import Lean.PaperLean.OLeanPack
import Lean.PaperLean.System
import Lean.Data.NameMap

/-!
Olean packs written during a build, for the `lean` processes that the build starts later. When Lake
runs for a `paperlean` command (`Lake.PaperLean.accelerated`), the workspace has no prepared data
(`Lake.PaperLean.Env`) and a build has compiled `minModules` modules, Lake packs the modules that the
build compiles, in batches as they finish (`moduleDone`),
and uses a pack of the toolchain's library, which it writes once into the user's cache directory
(or `PAPERLEAN_CACHE_DIR`; `toolchainPack`) and again only when the library changed. Every `lean`
that the build starts afterwards reads its imports from the packs written so far
(`Lake.PaperLean.BuildEnv`, `LEAN_OLEAN_PACK`). A pack only changes how files are read, so what a
module compiles to does not depend on which packs exist when it starts. (No import image is
written: an image of the toolchain's library alone makes the import of states with many entries of
other modules slower, as those are then replayed instead of folded.) The build's own packs are in
`.lake/paperlean/build/<process id>/` and are removed at the end of the build (`finish`), or by the
next build if this one was interrupted. `PAPERLEAN_BUILD_PACKS=0` turns this off,
`PAPERLEAN_BUILD_PACKS=1` packs from the first compiled module on.
-/

open System Lean

namespace Lake.PaperLean.BuildData

/-- The packs of this build. -/
structure State where
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

/-- `none` until this build packs; then the packs, or `none` forever if it does not. -/
private builtin_initialize stateRef : IO.Ref (Option (Option State)) ← IO.mkRef none

/-- The modules that this build compiles: only those are packed. -/
private builtin_initialize compiledRef : IO.Ref NameSet ← IO.mkRef {}

/-- The packs being written, which the end of the build waits for. -/
private builtin_initialize tasksRef : IO.Ref (Array (Task (Except IO.Error Unit))) ← IO.mkRef #[]

/-- The modules that the build compiled before it started packing, to be packed first. -/
private builtin_initialize earlyRef : IO.Ref (Array (String × Array (Array String))) ← IO.mkRef #[]

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

/-- How long a finished module waits for its batch (ms). -/
private def maxWait : Nat := 20000

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

/-- PaperLean's directory in the user's cache directory, or `PAPERLEAN_CACHE_DIR`. -/
private def cacheDir? : BaseIO (Option FilePath) := do
  if let some dir ← IO.getEnv "PAPERLEAN_CACHE_DIR" then
    return some (FilePath.mk dir)
  return (· / "paperlean") <$> (← getSystemCacheHome?)

/-- A stamp of the files of `chains`: their names, sizes and modification times. -/
private def stamp (chains : Array (Array String)) : IO UInt64 := do
  let mut h : UInt64 := 11
  for chain in chains do
    for f in chain do
      let m ← FilePath.metadata f
      h := mixHash h (hash f)
      h := mixHash h m.byteSize
      h := mixHash h (hash m.modified.sec)
      h := mixHash h m.modified.nsec.toUInt64
  return h

/-- The file holding this build's shared lock on the toolchain's pack, so that no other build
removes it while this one uses it. -/
private builtin_initialize lockRef : IO.Ref (Option IO.FS.Handle) ← IO.mkRef none

/-- The number of packs of other toolchains (or of earlier states of a toolchain) kept. -/
private def keptToolchainPacks : Nat := 2

/-- Removes from `dir` the temporary files of writers that ended before renaming theirs, and the packs
other than `current` beyond the `keptToolchainPacks` newest if no build uses them. -/
private def cleanToolchainPacks (dir current : FilePath) : IO Unit := do
  let mut others := #[]
  for d in ← dir.readDir do
    let f := d.fileName
    if let some pid := (f.splitOn ".tmp-").getLast?.bind (·.toNat?) then
      unless ← Lean.PaperLean.processAlive pid.toUInt32 do
        try IO.FS.removeFile d.path catch _ => pure ()
    else if f.endsWith ".paperlean" && d.path != current then
      try others := others.push (d.path, (← d.path.metadata).modified) catch _ => pure ()
  for (pack, _) in (others.qsort fun a b => compare a.2 b.2 == .gt)[keptToolchainPacks:] do
    try
      let h ← IO.FS.Handle.mk pack .read
      if ← h.tryLock (exclusive := true) then
        IO.FS.removeFile pack
        h.unlock
    catch _ => pure ()

/--
The pack of the toolchain's library `leanLibDir` in PaperLean's cache directory, used by later `lean`
processes of the build as soon as written. Its name holds a stamp of the library's files, so that a
pack is only used for the library as it was packed. It is written to a temporary file renamed into
place, so that concurrent builds see a whole pack.
-/
private def toolchainPack (leanLibDir : FilePath) : IO Unit := do
  let some cache ← cacheDir? | return
  let root := rootString leanLibDir
  let chains := (← chainsBelow leanLibDir).qsort fun a b => a[0]! < b[0]!
  if chains.isEmpty then return
  let dir := cache / "toolchain-packs"
  let name := s!"lib-{hash root}-{String.ofList (Nat.toDigits 16 (← stamp chains).toNat)}-{Lean.PaperLean.version}"
  let pack := dir / s!"{name}.paperlean"
  IO.FS.createDirAll dir
  cleanToolchainPacks dir pack
  for _ in [0:2] do
    unless ← pack.pathExists do
      let tmp := dir / s!"{name}.paperlean.tmp-{← IO.Process.getPID}"
      discard <| Lean.PaperLean.OLeanPack.createOf chains #[root] tmp toolchainBaseAddr
      IO.FS.rename tmp pack
    let h ← IO.FS.Handle.mk pack .read
    h.lock (exclusive := false)
    -- unless another build removed it before this one held the lock
    if ← pack.pathExists then
      lockRef.set (some h)
      BuildEnv.addPack pack.toString
      return

/-- Writes the pack `i` of `batch` in the background, then records it. -/
private def writePack (dir : FilePath) (i : Nat) (batch : Array (String × Array (Array String))) :
    BaseIO Unit := do
  let t ← IO.asTask (prio := .dedicated) do
    let out := dir / s!"pack-{i}.paperlean"
    let roots := batch.foldl (init := #[]) fun rs (r, _) => if rs.contains r then rs else rs.push r
    try
      discard <| Lean.PaperLean.OLeanPack.createOf (batch.flatMap (·.2)) roots out (baseAddr i)
      BuildEnv.addPack out.toString
    catch _ => pure ()
    stateRef.modify fun
      | some (some s) => some (some { s with writing := false })
      | st => st
  tasksRef.modify (·.push t)

/-- Starts writing a pack of the pending modules if they are enough or have waited long enough. -/
private def maybeWrite : BaseIO Unit := do
  let now ← IO.monoMsNow
  let job? ← stateRef.modifyGet fun
    | some (some s) =>
      if s.writing || s.pending.isEmpty ||
          (s.pending.size < minBatch s && now - s.pendingSince < maxWait) then
        (none, some (some s))
      else
        (some (s.dir, s.started, s.pending),
          some (some { s with pending := #[], packed := s.packed + s.pending.size, writing := true,
                              started := s.started + 1 }))
    | st => (none, st)
  if let some (dir, i, batch) := job? then
    writePack dir i batch

/-- Decides whether this build packs, and if so, starts using the toolchain's pack (in the
background) and packs the modules compiled so far. -/
private def start (wsDir leanLibDir : FilePath) : IO Unit := do
  let disabled := !(← accelerated) || (← IO.getEnv "PAPERLEAN_BUILD_PACKS") == some "0" ||
    (← IO.getEnv dataMarker).isSome || (← explicitDataVars)
  let state? ← if disabled then pure none else do
    let base := dataDir wsDir / "build"
    -- the packs of earlier builds whose process ended
    if ← base.pathExists then
      for d in ← base.readDir do
        if let some pid := d.fileName.toNat? then
          unless ← Lean.PaperLean.processAlive pid.toUInt32 do
            try IO.FS.removeDirAll d.path catch _ => pure ()
    let dir := base / toString (← IO.Process.getPID)
    let batch? := (← IO.getEnv "PAPERLEAN_BUILD_PACK_BATCH").bind (·.toNat?)
    try
      IO.FS.createDirAll dir
      pure (some ({ dir, batch? } : State))
    catch _ => pure none
  let first ← stateRef.modifyGet fun st => if st.isSome then (false, st) else (true, some state?)
  unless first && state?.isSome do return
  let t ← IO.asTask (prio := .dedicated) (toolchainPack leanLibDir)
  tasksRef.modify (·.push t)
  let early ← earlyRef.swap #[]
  let now ← IO.monoMsNow
  stateRef.modify fun
    | some (some s) => some (some { s with pending := early ++ s.pending, pendingSince := now })
    | st => st
  maybeWrite

/-- Called before the build compiles the module `mod` of the workspace in `wsDir`, whose toolchain's
library is `leanLibDir`: starts packing once the build has compiled enough modules. -/
public def compileStarting (mod : Module) (wsDir leanLibDir : FilePath) : IO Unit := do
  let n ← compiledRef.modifyGet fun s => let s := s.insert mod.name; (s.size, s)
  match ← stateRef.get with
  | some _ => maybeWrite
  | none =>
    if n ≥ minModules || (← IO.getEnv "PAPERLEAN_BUILD_PACKS") == some "1" then
      start wsDir leanLibDir

/-- Called when the build is done with `mod` (its files are final): packs it with the next batch if
the build compiled it. -/
public def moduleDone (mod : Module) : IO Unit := do
  if (← stateRef.get) matches some none then return
  unless (← compiledRef.get).contains mod.name do return
  let chains ← chainsOf mod
  if chains.isEmpty then return
  let entry := (rootString mod.pkg.leanLibDir, chains)
  let now ← IO.monoMsNow
  let early ← stateRef.modifyGet fun
    | some (some s) =>
      (false, some (some { s with pending := s.pending.push entry,
                                  pendingSince := if s.pending.isEmpty then now else s.pendingSince }))
    | st => (st.isNone, st)
  if early then
    earlyRef.modify (·.push entry)
  else
    maybeWrite

/-- Called at the end of a build: waits for the packs being written and removes those of the build,
which no process needs any more (unless `PAPERLEAN_BUILD_PACKS_KEEP` is set, for tests). -/
public def finish : BaseIO Unit := do
  for t in ← tasksRef.swap #[] do
    discard <| IO.wait t
  BuildEnv.clear
  lockRef.set none
  earlyRef.set #[]
  compiledRef.set {}
  let st ← stateRef.swap none
  if let some (some s) := st then
    if (← IO.getEnv "PAPERLEAN_BUILD_PACKS_KEEP").isNone then
      discard <| (IO.FS.removeDirAll s.dir).toBaseIO

end Lake.PaperLean.BuildData
