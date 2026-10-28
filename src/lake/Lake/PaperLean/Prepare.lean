/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
import Init
public import Lake.Config.Workspace
public import Lake.Util.Log
import Lake.Config.Module
import Lake.Config.LeanLib
import Lake.Util.Lock
public import Lake.PaperLean.Env
import Lake.PaperLean.Native
import Lean.PaperLean.OLeanPack
import Lean.PaperLean.System
import Std.Data.HashMap
import Lean.Data.NameMap
import Lean.Elab.ParseImportsFast

/-!
`paperlean prepare`: writes a workspace's prepared data (`Lake.PaperLean.Env`): an olean pack of the
dependency packages and the toolchain's `lib/lean`, its import image and the native libraries of the
dependency packages, and, if asked, a pack of the root package. Everything is checked first. Each run
writes a new directory (`deps-<stamp>/`, `root-<stamp>/`) and then switches `env.json` to it, so that
processes still using the old data keep it and an interrupted run leaves the old data intact; the
next run deletes directories that `env.json` does not refer to.
-/

open System Lean

namespace Lake.PaperLean

/-- The dependency packages of `ws`, dependencies first. -/
public partial def dependencies (ws : Workspace) : Array Package := Id.run do
  let rootName := ws.root.baseName
  let rec visit (pkg : Package) (out : Array Package) : Array Package :=
    if pkg.baseName == rootName || out.any (·.baseName == pkg.baseName) then out
    else (pkg.depPkgs.foldl (fun out dep => visit dep out) out).push pkg
  return ws.packages.foldl (fun out pkg => visit pkg out) #[]

/-- The packages that `pkg` depends on directly or indirectly. -/
partial def closure (pkg : Package) : Array Name :=
  let rec go (pkg : Package) (out : Array Name) : Array Name :=
    pkg.depPkgs.foldl (init := out) fun out dep =>
      if out.contains dep.baseName then out else go dep (out.push dep.baseName)
  go pkg #[]

/-- The modules of `pkg` that `lake build` of the package builds: those of its default libraries, or
of all of its libraries if it has no default targets. -/
public def defaultModules (pkg : Package) : IO (Array Module) := do
  let libs := pkg.leanLibs.filter fun lib =>
    pkg.defaultTargets.isEmpty || pkg.defaultTargets.contains lib.name
  let mut mods : Array Module := #[]
  let mut seen : NameSet := {}
  for lib in libs do
    for mod in ← lib.getModuleArray do
      unless seen.contains mod.name do
        seen := seen.insert mod.name
        mods := mods.push mod
  return mods

/-- The modules of the dependency packages that the root package's modules import directly or
indirectly, by their sources' headers (as Lake reads them; a header that cannot be parsed is
skipped, as `lake build` reports it). -/
public partial def importedDependencyModules (ws : Workspace) : IO (Array Module) := do
  let mut todo ← defaultModules ws.root
  let mut seen : NameSet := todo.foldl (·.insert ·.name) {}
  let mut out := #[]
  while h : todo.size > 0 do
    let mod := todo.back
    todo := todo.pop
    if mod.pkg.baseName != ws.root.baseName then out := out.push mod
    unless ← mod.leanFile.pathExists do continue
    let some header ← (some <$> Lean.parseImports' (← IO.FS.readFile mod.leanFile) mod.leanFile.toString)
      <|> pure none | continue
    for imp in header.imports do
      -- Lean's own modules are not in the workspace
      if let some dep := ws.findModule? imp.module then
        unless seen.contains dep.name do
          seen := seen.insert dep.name
          todo := todo.push dep
  return out

/-- The total size of the files below `root` with an extension in `exts`. -/
def filesSize (root : FilePath) (exts : Array String) : IO Nat := do
  unless ← root.isDir do return 0
  let mut n := 0
  for p in ← root.walkDir do
    if exts.any (p.toString.endsWith ·) then
      n := n + (← p.metadata).byteSize.toNat
  return n

/-- `n` bytes for people. -/
public def showBytes (n : Nat) : String :=
  if n ≥ 1000000000 then s!"{n / 100000000 / 10}.{n / 100000000 % 10} GB"
  else if n ≥ 1000000 then s!"{n / 1000000} MB"
  else s!"{n / 1000} kB"

/-- `ms` milliseconds for people. -/
def showTime (ms : Nat) : String :=
  let s := ms / 1000
  if s ≥ 60 then s!"{s / 60}m{s % 60}s" else s!"{s}s"

/-- What to prepare. -/
public structure PrepareOptions where
  /-- Also a pack of the root package's modules. -/
  root : Bool := false
  /-- The native libraries of the dependency packages. -/
  native : Bool := true
  /-- Compiler processes at once; `0`: automatic. -/
  jobs : Nat := 0
  /-- The dependency packages to prepare in full, with the packages they depend on that are not
  prepared yet, keeping the data of the other prepared packages; `none`: all dependency packages, in
  full. -/
  packages : Option (Array Package) := none

/-- The name by which `env.json` records the package `pkg`. -/
public def pkgKey (pkg : Package) : String := pkg.baseName.toString (escape := false)

/-- The dependency packages whose data `d` holds. -/
public def preparedPackages (ws : Workspace) (d : PreparedData) : Array String :=
  d.packages?.getD ((dependencies ws).map pkgKey)

/-- What `prepare` writes of the dependencies: the packages whose data it holds afterwards
(dependencies first), and those whose native libraries it builds. Without names (`named`), all
dependency packages, all built. With names, the named packages and the packages they depend on (with
`root`, all dependency packages), and the packages prepared before (`before`); the libraries built are
those of the named packages, of the packages without one in `libs` and of those that depend on a
package whose library is built. -/
def plan (allDeps : Array Package) (before : Array String) (libs : Array PreparedNative)
    (named : Option (Array Package)) (root : Bool) : Array Package × Array String := Id.run do
  let some named := named | return (allDeps, allDeps.map pkgKey)
  let mut want := before
  for p in named ++ (if root then allDeps else #[]) do
    for n in (closure p).push p.baseName do
      let k := n.toString (escape := false)
      unless want.contains k do want := want.push k
  let deps := allDeps.filter fun p => want.contains (pkgKey p)
  let mut built : Array String := #[]
  for p in deps do
    if named.any (·.baseName == p.baseName) || !libs.any (·.pkg == pkgKey p) ||
        (closure p).any fun n => built.contains (n.toString (escape := false)) then
      built := built.push (pkgKey p)
  return (deps, built)

/-- The address at which the root package's pack is mapped, disjoint from the dependency pack's. -/
def rootPackBase : USize := 0x240000000000

/-- The Lean program that writes an import image (`Lean.PaperLean.writeImportImage`) of the pack in
`LEAN_OLEAN_PACK` after importing the modules listed in a file. -/
def imageProgram : String := "import Lean.PaperLean.ImportState
open Lean
def main (args : List String) : IO UInt32 := do
  let [out, modsFile] := args | return 2
  initSearchPath (← findSysroot (lean := (← IO.appPath).toString))
  unsafe enableInitializersExecution
  let mods := (← IO.FS.lines modsFile).filter (· ≠ \"\")
  let _env ← importModules (mods.map fun m => { module := m.toName }) {} (loadExts := true)
  IO.println s!\"{← PaperLean.writeImportImage out}\"
  return 0
"

/-- The compiler processes to run at once: at most one per hardware thread and per 2 GB of memory. -/
def autoJobs : BaseIO Nat := do
  let cpus ← Lean.PaperLean.numCPUs
  let mem ← Lean.PaperLean.totalMemory
  return max 1 (if mem == 0 then cpus else min cpus (mem / 2000000000))

/-- How a pack in `.lake/paperlean/<dir>/` of `ws` records `roots`: those in the workspace relative to
it (`Lean.PaperLean.OLeanPack.create`), so that a moved project keeps its packs. -/
def storedRootsFor (ws : Workspace) (roots : Array FilePath) : Array String :=
  let wsDir := ws.dir.toString ++ "/"
  roots.map fun r =>
    let r := (r.toString.dropEndWhile (· == '/')).toString
    match r.dropPrefix? wsDir with
    | some rest => "^3/" ++ rest.toString
    | none => r

/-- Whether a file below the library directory of one of `pkgs` belongs to a current module: one of
the package's libraries has the module and its source exists. Lake keeps the files of modules that
no longer exist (e.g. after an update renamed them); packs leave them out, which changes nothing, as
files that are not packed are read from the disk. Files below other directories are kept. -/
def currentArtifact (pkgs : Array Package) : IO (String → IO Bool) := do
  let known ← IO.mkRef ({} : Std.HashMap String Bool)
  let exts := [".olean.server", ".olean.private", ".olean", ".ir.sig", ".ir"]
  return fun f => do
    let some pkg := pkgs.find? (f.startsWith ·.leanLibDir.toString) | return true
    let rel := (f.drop (pkg.leanLibDir.toString.length + 1)).toString
    let stem := (exts.findSome? (rel.dropSuffix? ·)).map (·.toString) |>.getD rel
    if let some b := (← known.get).get? stem then return b
    let name := (stem.splitOn "/").foldl (init := Name.anonymous) Name.mkStr
    let b ← match pkg.findModule? name with
      | some mod => mod.leanFile.pathExists
      | none => pure false
    known.modify (·.insert stem b)
    return b

/-- The writing part of `prepare`, into the new directories of `stamp`: unless `keepDeps` (then those
of `old?` stay), the dependency pack and import image of `deps` and their native libraries, built for
the packages of `built` and kept from `old?` for the others; the root package's pack if
`opts.root`, else that of `old?`. -/
def prepareIn (ws : Workspace) (opts : PrepareOptions) (dir : FilePath) (stamp : String)
    (deps : Array Package) (built : Array String) (keepDeps : Bool) (depRoots : Array FilePath)
    (depMods : Array Module) (rootMods rootUnbuilt : Nat) (native : Bool) (old? : Option PreparedData) :
    LoggerIO UInt32 := do
    let stored := storedRootsFor ws
    let depDirName := s!"deps-{stamp}"
    let depDir := dir / depDirName
    let nativeDirName := s!"native-{stamp}"
    let oldLibs := old?.bind (·.libs?) |>.getD #[]
    let mut packs : Array String := #[]
    let mut image? : Option String := none
    let mut libs : Array PreparedNative := #[]
    let mut summary : Array String := #[]
    let mut failed : Array String := #[]
    if keepDeps then
      if let some old := old? then
        packs := old.packs.filter (!·.startsWith "root-")
        image? := old.image?
        libs := oldLibs
        summary := old.summary
    else if !deps.isEmpty then
      IO.FS.createDirAll depDir
      let start ← IO.monoMsNow
      IO.println s!"Packing {deps.size} dependency packages and Lean's library..."
      let n ← Lean.PaperLean.OLeanPack.create depRoots (depDir / "deps.paperlean") (storedRoots := stored depRoots)
        (keep := ← currentArtifact deps)
      IO.println s!"  {n} files ({showTime ((← IO.monoMsNow) - start)})"
      packs := #[s!"{depDirName}/deps.paperlean"]
      -- The image describes the dependency pack, as importing all dependency modules builds it.
      let start ← IO.monoMsNow
      IO.println s!"Writing the import image of {depMods.size} modules..."
      let tmp := depDir / "tmp"
      IO.FS.createDirAll tmp
      IO.FS.writeFile (tmp / "Image.lean") imageProgram
      IO.FS.writeFile (tmp / "modules.txt") ("\n".intercalate (depMods.map (·.name.toString)).toList)
      let out ← IO.Process.output {
        cmd := ws.lakeEnv.lean.lean.toString
        args := #["--run", (tmp / "Image.lean").toString, (depDir / "deps.image.paperlean").toString,
          (tmp / "modules.txt").toString]
        env := #[("LEAN_OLEAN_PACK", some (depDir / "deps.paperlean").toString), ("LEAN_IMPORT_IMAGE", none),
          ("PAPERLEAN_NATIVE_LIBS", none), ("LEAN_PATH", some ws.augmentedLeanPath.toString)]
      }
      IO.FS.removeDirAll tmp
      if out.exitCode == 0 then
        image? := some s!"{depDirName}/deps.image.paperlean"
        IO.println s!"  {(out.stdout.dropEndWhile Char.isWhitespace).toString} entries \
          ({showTime ((← IO.monoMsNow) - start)})"
      else
        IO.eprintln s!"paperlean: warning: no import image, as writing it failed:\n{out.stderr}"
      -- Native libraries, dependencies first: built for the packages of `built`, kept for the others
      -- (whose libraries, and those they are linked against, are as they were). A package is skipped
      -- if its library cannot be built.
      let jobs ← if opts.jobs > 0 then pure opts.jobs else autoJobs
      for pkg in deps do
        let key := pkgKey pkg
        unless built.contains key do
          if let some lib := oldLibs.find? (·.pkg == key) then
            libs := libs.push lib
            if let some line := old?.bind fun old => old.summary.find? (·.startsWith s!"{pkg.prettyName}: ") then
              summary := summary.push line
          continue
        unless native do continue
        let needs := (closure pkg).map (·.toString (escape := false))
        if let some dep := needs.find? fun d => deps.any (pkgKey · == d) && !libs.any (fun l => l.pkg == d && !l.failed) then
          IO.eprintln s!"paperlean: skipping the native library of {pkg.prettyName}: {dep} has none"
          summary := summary.push s!"{pkg.prettyName}: not built ({dep} has no native library)"
          failed := failed.push pkg.prettyName
          libs := libs.push { pkg := key, manifest := "", lib := "", modules := 0, failed := true }
          continue
        let depLibs : Array NativeLib := libs.filter (fun l => needs.contains l.pkg && l.modules > 0) |>.map fun l =>
          { pkg := l.pkg.toName, lib := dir / l.lib, manifest := dir / l.manifest, modules := l.modules, excluded := #[] }
        let start ← IO.monoMsNow
        let last ← IO.mkRef 0
        let progress (done total : Nat) : BaseIO Unit := do
          let now ← IO.monoMsNow
          if done == total || now - (← last.get) ≥ 5000 then
            last.set now
            let eta := if done == 0 || done == total then "" else
              s!", about {showTime ((now - start) * (total - done) / done)} left"
            (IO.println s!"  {pkg.prettyName}: {done} of {total} modules{eta}").catchExceptions fun _ => pure ()
        IO.println s!"Compiling the native library of {pkg.prettyName} ({jobs} jobs)..."
        let (lib?, log) ← (buildNativeLib ws pkg depLibs (dir / nativeDirName) jobs progress).captureLog
        log.replay
        let some lib := lib?
          | -- the first line of the error, for the summary and `status`
            let why := (log.entries.find? (·.level == .error)).map (·.message.splitOn "\n" |>.head!) |>.getD "error"
            IO.eprintln s!"paperlean: the native library of {pkg.prettyName} could not be built (the error above)"
            summary := summary.push s!"{pkg.prettyName}: not built ({why})"
            failed := failed.push pkg.prettyName
            libs := libs.push { pkg := key, manifest := "", lib := "", modules := 0, failed := true }
        if lib.modules == 0 then
          libs := libs.push { pkg := key, manifest := "", lib := "", modules := 0 }
          IO.println "  no built modules"
          continue
        libs := libs.push {
          pkg := key, modules := lib.modules
          manifest := s!"{nativeDirName}/{lib.manifest.fileName.getD ""}"
          lib := s!"{nativeDirName}/{lib.lib.fileName.getD ""}" }
        let excl := if lib.excluded.isEmpty then "" else s!", {lib.excluded.size} left out"
        summary := summary.push s!"{pkg.prettyName}: {lib.modules} modules{excl}"
        IO.println s!"  {lib.modules} modules{excl} ({showTime ((← IO.monoMsNow) - start)})"
        if let some (m, why) := lib.excluded[0]? then
          IO.println s!"  e.g. {m}: {why}"
      if ← (dir / nativeDirName / "obj").isDir then
        IO.FS.removeDirAll (dir / nativeDirName / "obj")
    if opts.root then
      let rootDirName := s!"root-{stamp}"
      IO.FS.createDirAll (dir / rootDirName)
      let n ← Lean.PaperLean.OLeanPack.create #[ws.root.leanLibDir] (dir / rootDirName / "root.paperlean")
        rootPackBase (stored #[ws.root.leanLibDir]) (← currentArtifact #[ws.root])
      IO.println s!"Packed {n} files of {ws.root.prettyName} ({rootMods} modules built\
        {if rootUnbuilt > 0 then s!", {rootUnbuilt} not built yet" else ""})"
      packs := packs.push s!"{rootDirName}/root.paperlean"
    else if let some old := old? then
      -- the root package's pack (with the pack of its changes, if any) is refreshed on its own
      for p in old.packs.filter (·.startsWith "root-") do
        if ← (dir / p).pathExists then packs := packs.push p
    -- (a library that a failed one's dependents would need is never used, so it is not listed)
    let usable := libs.filter fun l => l.modules > 0 && !l.failed
    let data : PreparedData := {
      paperlean := Lean.PaperLean.version, githash := Lean.githash, platform := System.Platform.target
      packs, image?, summary
      native := usable.map (·.manifest)
      packages? := some (deps.map pkgKey)
      libs? := some libs }
    data.write (dir / "env.json.tmp")
    IO.FS.rename (dir / "env.json.tmp") (dir / "env.json")
    -- the directories that `env.json` no longer refers to
    let used := packs ++ image?.toArray ++ usable.map (·.manifest) ++ usable.map (·.lib)
    for e in ← dir.readDir do
      if (e.fileName.startsWith "deps-" || e.fileName.startsWith "root-" ||
          e.fileName.startsWith "native-" || e.fileName == "tmp") &&
          !used.any (·.startsWith (e.fileName ++ "/")) then
        IO.FS.removeDirAll e.path
    IO.println s!"Prepared {dir}."
    unless failed.isEmpty do
      IO.eprintln s!"paperlean: warning: no native library for {", ".intercalate failed.toList} (see above), \
        so their code runs in the interpreter: the same results, but slower. `paperlean status` shows \
        this too."
    return 0

/-- The modules of `deps` whose files the import image describes: those that the root package's
modules import (all of the packages' modules if they import none). -/
def imageModules (ws : Workspace) (deps : Array Package) : IO (Array Module × Array Module) := do
  let imported := (← importedDependencyModules ws).filter fun m => deps.any (·.baseName == m.pkg.baseName)
  let candidates ← if imported.isEmpty then (deps.flatMapM defaultModules : IO (Array Module)) else pure imported
  return (imported, candidates)

/-- The disk space that packing the files below `depRoots` and compiling the native libraries of the
packages `built` of `deps` needs, and packing the root package if `root`. -/
def neededSpace (ws : Workspace) (deps : Array Package) (depRoots : Array FilePath) (built : Array String)
    (root native : Bool) : IO Nat := do
  -- the packs copy the files; a native library is about half the size of its C files
  let packExts := #[".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir"]
  let mut need := 0
  for r in depRoots do need := need + (← filesSize r packExts)
  if root then need := need + (← filesSize ws.root.leanLibDir packExts)
  if native then
    for pkg in deps do
      if built.contains (pkgKey pkg) then need := need + (← filesSize pkg.irDir #[".c"])
  return need

/-- Whether `need` bytes fit into the free space of `dir`; says why not if not. -/
def enoughSpace (dir : FilePath) (need : Nat) (what : String) : IO Bool := do
  IO.FS.createDirAll dir
  -- `PAPERLEAN_FREE_SPACE` (bytes) replaces the measured free space, for tests
  let free ← match (← IO.getEnv "PAPERLEAN_FREE_SPACE").bind String.toNat? with
    | some n => pure n
    | none => Lean.PaperLean.freeSpace dir.toString
  if need + need / 10 > free then
    IO.eprintln s!"paperlean: {what} needs about {showBytes (need + need / 10)} of disk space in {dir}, \
      but only {showBytes free} are free. Nothing was changed."
    return false
  return true

/-- Runs `act` holding the lock of the prepared data in `dir` if `env.json` is still `text?`, which
the command read before: otherwise another command changed it meanwhile, and nothing is done. -/
def withUnchangedData (ws : Workspace) (text? : Option String) (act : LoggerIO UInt32) : LoggerIO UInt32 :=
  withDataLock (dataDir ws.dir) do
    if (← preparedDataText ws.dir) != text? then
      IO.eprintln "paperlean: another paperlean command changed the prepared data meanwhile; run the \
        command again. Nothing was changed."
      return 1
    act

/-- Prepares the data of `ws`; the exit code. -/
public def prepare (ws : Workspace) (opts : PrepareOptions) : LoggerIO UInt32 := do
  let dir := dataDir ws.dir
  let allDeps := dependencies ws
  let leanLib := ws.lakeEnv.lean.leanLibDir
  let text? ← preparedDataText ws.dir
  let old? : Option PreparedData := match ← readPreparedData ws.dir with
    | some (.ok d) => if d.mismatch?.isNone then some d else none
    | _ => none
  let before := old?.map (preparedPackages ws) |>.getD #[]
  let (deps, built) := plan allDeps before (old?.bind (·.libs?) |>.getD #[]) opts.packages opts.root
  -- the dependency data stays as it is if it holds these packages and no library is built again
  let keepDeps := old?.isSome && opts.packages.isSome && built.isEmpty &&
    deps.size == before.size && deps.all (before.contains <| pkgKey ·)
  if keepDeps && !opts.root then
    IO.println s!"{", ".intercalate ((opts.packages.getD #[]).map (·.prettyName)).toList} and the \
      packages they depend on are prepared already."
    return 0
  -- The dependency modules that the root package imports must be built: their packed files are
  -- what imports read. (Without root modules, the built modules of the dependencies.)
  let (imported, candidates) ← imageModules ws deps
  let mut missing := 0
  let mut missingEx := #[]
  let mut depMods : Array Module := #[]
  for mod in candidates do
    if ← mod.oleanFile.pathExists then
      depMods := depMods.push mod
    else if !imported.isEmpty then
      missing := missing + 1
      if missingEx.size < 3 then missingEx := missingEx.push mod.name
  if missing > 0 && !keepDeps then
    IO.eprintln s!"paperlean: {missing} modules of the dependencies that {ws.root.prettyName} imports are not built, e.g. \
      {", ".intercalate (missingEx.map toString).toList}.\n\
      Download them with `paperlean cache get` or build them with `lake build`, then run \
      `paperlean prepare` again. Nothing was changed."
    return 1
  let mut rootMods := 0
  let mut rootUnbuilt := 0
  if opts.root then
    for mod in ← defaultModules ws.root do
      if ← mod.oleanFile.pathExists then rootMods := rootMods + 1
      else rootUnbuilt := rootUnbuilt + 1
  -- `PAPERLEAN_NO_NATIVE_PLATFORM` (any value) makes this build act as one without native
  -- libraries, for tests
  let available := Lean.PaperLean.nativeLibsAvailable &&
    (← IO.getEnv "PAPERLEAN_NO_NATIVE_PLATFORM").isNone
  if opts.native && !available && !keepDeps then
    IO.println s!"Native libraries are not available for {Platform.target} yet; preparing everything \
      else."
  let native := opts.native && available
  -- (a dependency that nothing built has no library directory)
  let depRoots ← if deps.isEmpty then pure #[] else
    (deps.map (·.leanLibDir) |>.push leanLib).filterM (·.isDir)
  let need ← neededSpace ws deps (if keepDeps then #[] else depRoots) (if keepDeps then #[] else built)
    opts.root native
  unless ← enoughSpace dir need "preparing" do return 1
  withUnchangedData ws text? do
    let stamp := toString (← IO.monoMsNow)
    try prepareIn ws opts dir stamp deps built keepDeps depRoots depMods rootMods rootUnbuilt native old?
    catch e =>
      -- the data that `env.json` refers to is untouched
      for d in [dir / s!"deps-{stamp}", dir / s!"native-{stamp}", dir / s!"root-{stamp}"] do
        if ← d.isDir then IO.FS.removeDirAll d
      throw e

/-- `paperlean clean` of the dependency packages `pkgs`: deletes their prepared data and that of the
prepared packages that depend on them. The others keep theirs: the dependency pack and its image are
written again without them, and their native libraries stay. -/
public def cleanPackages (ws : Workspace) (pkgs : Array Package) : LoggerIO UInt32 := do
  let dir := dataDir ws.dir
  let text? ← preparedDataText ws.dir
  let some (.ok old) ← readPreparedData ws.dir
    | IO.println "There is no prepared data."; return 0
  if let some why := old.mismatch? then
    IO.eprintln s!"paperlean: the prepared data cannot be used ({why}); `paperlean clean` deletes all of \
      it. Nothing was deleted."
    return 1
  let allDeps := dependencies ws
  let before := preparedPackages ws old
  let names := pkgs.map pkgKey
  let removed := allDeps.filter fun p => before.contains (pkgKey p) &&
    (names.contains (pkgKey p) || (closure p).any (names.contains <| ·.toString (escape := false)))
  if removed.isEmpty then
    IO.println s!"{", ".intercalate (pkgs.map (·.prettyName)).toList}: not prepared; nothing was deleted."
    return 0
  let deps := allDeps.filter fun p => before.contains (pkgKey p) && !removed.any (·.baseName == p.baseName)
  let (_, candidates) ← imageModules ws deps
  let depMods ← candidates.filterM (·.oleanFile.pathExists)
  let depRoots ← if deps.isEmpty then pure #[] else
    (deps.map (·.leanLibDir) |>.push ws.lakeEnv.lean.leanLibDir).filterM (·.isDir)
  unless ← enoughSpace dir (← neededSpace ws deps depRoots #[] false false) "packing the other packages" do
    return 1
  let others := removed.filter fun p => !pkgs.any (·.baseName == p.baseName)
  let code ← withUnchangedData ws text? do
    let stamp := toString (← IO.monoMsNow)
    try prepareIn ws {} dir stamp deps #[] false depRoots depMods 0 0 false (some old)
    catch e =>
      for d in [dir / s!"deps-{stamp}"] do
        if ← d.isDir then IO.FS.removeDirAll d
      throw e
  if code == 0 then
    IO.println s!"Deleted the prepared data of {", ".intercalate (removed.map (·.prettyName)).toList}\
      {if others.isEmpty then "" else
        s!" ({", ".intercalate (others.map (·.prettyName)).toList} depend on the named packages)"}."
  return code

/-- The address at which the pack of the root package's changes (`refresh`) is mapped. -/
def rootDeltaBase : USize := 0x280000000000

/-- The `.olean` files of `pkg`'s current modules that the packs `packs` (in this order) do not
serve, as they changed or were added since packing, and the number of its current modules. -/
public def packStaleness (pkg : Package) (packs : Array FilePath) : IO (Nat × Nat) := do
  let fresh : Std.HashSet String := (← Lean.PaperLean.OLeanPack.freshFiles packs pkg.leanLibDir).foldl
    (·.insert ·) {}
  let current ← currentArtifact #[pkg]
  let mut stale := 0
  let mut total := 0
  if ← pkg.leanLibDir.isDir then
    for p in ← pkg.leanLibDir.walkDir do
      if p.extension == some "olean" && (← current p.toString) then
        total := total + 1
        unless fresh.contains (p.toString.drop (pkg.leanLibDir.toString.length + 1)).toString do
          stale := stale + 1
  return (stale, total)

/-- The root package's pack in `d`, and the pack of its changes (`refresh`) if there is one. -/
public def rootPacks (d : PreparedData) : Option String × Option String :=
  (d.packs.find? (·.endsWith "/root.paperlean"), d.packs.find? (·.endsWith ".delta.paperlean"))

/-- `paperlean build --prepare`: packs the files of the root package's current modules that its
pack does not serve, as they changed or were added since it was written, into a pack of their own
that replaces the previous one; the root package's pack itself is not rewritten. Writes the root
package's pack if it has none, and prepares everything if nothing is prepared. -/
public def refresh (ws : Workspace) : LoggerIO UInt32 := do
  let dir := dataDir ws.dir
  let text? ← preparedDataText ws.dir
  let some (.ok d) ← readPreparedData ws.dir
    | IO.println "Nothing is prepared yet; preparing everything."
      prepare ws { root := true }
  if let some why := d.mismatch? then
    IO.println s!"The prepared data cannot be used ({why}); preparing everything."
    return ← prepare ws { root := true }
  let root := ws.root.leanLibDir
  unless ← root.isDir do
    IO.println s!"{ws.root.prettyName} has no built modules yet; nothing to pack."
    return 0
  let (base?, delta?) := rootPacks d
  -- the files to pack: all of the root package's current modules if it has no pack yet, otherwise
  -- those that its pack does not serve
  let fresh : Std.HashSet String ← match base? with
    | some base => (·.foldl (·.insert ·) {}) <$> Lean.PaperLean.OLeanPack.freshFiles #[dir / base] root
    | none => pure {}
  let current ← currentArtifact #[ws.root]
  let exts := #[".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir"]
  let mut files : Std.HashSet String := {}
  let mut need := 0
  for p in ← root.walkDir do
    let f := p.toString
    if exts.any (f.endsWith ·) && !fresh.contains (f.drop (root.toString.length + 1)).toString &&
        (← current f) then
      files := files.insert f
      need := need + (← p.metadata).byteSize.toNat
  let free ← match (← IO.getEnv "PAPERLEAN_FREE_SPACE").bind String.toNat? with
    | some n => pure n
    | none => Lean.PaperLean.freeSpace dir.toString
  if need + need / 10 > free then
    IO.eprintln s!"paperlean: packing the changed modules needs about {showBytes (need + need / 10)} of \
      disk space in {dir}, but only {showBytes free} are free. Nothing was changed."
    return 1
  withUnchangedData ws text? do
    let stamp := toString (← IO.monoMsNow)
    let start ← IO.monoMsNow
    let keep (f : String) : IO Bool := pure (files.contains f)
    let (file?, packs) ← match base? with
      | none =>
        -- the root package's first pack
        let rel := s!"root-{stamp}/root.paperlean"
        IO.FS.createDirAll (dir / s!"root-{stamp}")
        let n ← Lean.PaperLean.OLeanPack.create #[root] (dir / rel) rootPackBase (storedRootsFor ws #[root]) keep
        IO.println s!"Packed {n} files of {ws.root.prettyName} ({showTime ((← IO.monoMsNow) - start)})."
        pure (some rel, d.packs.push rel)
      | some base =>
        let (stale, total) ← packStaleness ws.root #[dir / base]
        let others := d.packs.filter (some · != delta?)
        if files.isEmpty then
          IO.println s!"Nothing of {ws.root.prettyName} changed since its pack was written."
          pure (none, others)
        else
          let rel := s!"{(base : FilePath).parent.get!}/changes-{stamp}.delta.paperlean"
          let n ← Lean.PaperLean.OLeanPack.create #[root] (dir / rel) rootDeltaBase
            (storedRootsFor ws #[root]) keep
          IO.println s!"Packed {n} files of the {stale} of {total} modules of {ws.root.prettyName} that \
            changed or were added since its pack was written ({showTime ((← IO.monoMsNow) - start)})."
          if 2 * stale > total then
            IO.println s!"(`paperlean prepare {ws.root.prettyName}` packs them all again, which reads a \
              little faster.)"
          -- before the root package's pack, so that it serves the files that changed
          pure (some rel, others.flatMap fun p => if some p == base? then #[rel, p] else #[p])
    let data := { d with packs }
    data.write (dir / "env.json.tmp")
    IO.FS.rename (dir / "env.json.tmp") (dir / "env.json")
    if let some old := delta? then
      if some old != file? && (← (dir / old).pathExists) then IO.FS.removeFile (dir / old)
    return 0

end Lake.PaperLean
