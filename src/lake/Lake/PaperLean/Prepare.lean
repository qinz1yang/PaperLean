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
public import Lake.PaperLean.Env
import Lake.PaperLean.Native
import Lake.PaperLean.BuildData
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
partial def closurePackages (pkg : Package) : Array Package :=
  let rec go (pkg : Package) (out : Array Package) : Array Package :=
    pkg.depPkgs.foldl (init := out) fun out dep =>
      if out.any (·.baseName == dep.baseName) then out else go dep (out.push dep)
  go pkg #[]

/-- The names of `closurePackages`. -/
def closure (pkg : Package) : Array Name :=
  (closurePackages pkg).map (·.baseName)

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

/-- Those of `modules` that import one of `below` directly or indirectly, leaving out `below`: a
module runs in the interpreter if one of its imports does. By their sources' headers. -/
def importersIn (modules : Array Module) (below : NameSet) : IO (Array Name) := do
  if below.isEmpty then return #[]
  let mut mods : Array (Name × Array Name) := #[]
  for mod in modules do
    unless ← mod.leanFile.pathExists do continue
    let some header ← (some <$> Lean.parseImports' (← IO.FS.readFile mod.leanFile) mod.leanFile.toString)
      <|> pure none | continue
    mods := mods.push (mod.name, header.imports.map (·.module))
  let mut reached := below
  let mut out := #[]
  let mut changed := true
  while changed do
    changed := false
    for (m, imports) in mods do
      if !reached.contains m && imports.any reached.contains then
        reached := reached.insert m
        out := out.push m
        changed := true
  return out

/-- The built modules of `pkg` in libraries that Lake loads as plugins for whatever imports them. -/
def pluginModules (pkg : Package) : IO (Array Name) := do
  unless pkg.leanLibs.any (·.shouldPrecompile) do return #[]
  return ((← builtModules pkg).filter (·.lib.shouldPrecompile)).map (·.name)

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

/-- `lib`, the native library of `pkg` that a new dependency pack keeps, with what was found of its
modules only for those whose files are still those of `oldPack`, the pack that it holds for: the others
are `outdated`, and the new pack then holds of what `lib` says only what was found of its files. A
module that did not change and imports one that runs in the interpreter still does: the libraries of the
packages it depends on stay too, so that nothing gives the module that it imports native code. -/
public def keptFindings (pkg : Package) (oldPack : FilePath) (lib : PreparedNative) : IO PreparedNative := do
  let names := lib.interpreted.map (·.1) ++ lib.importers ++ lib.plugin.map (·.1)
  if names.isEmpty then return lib
  let fresh : Std.HashSet String := (← Lean.PaperLean.OLeanPack.freshFiles #[oldPack] pkg.leanLibDir).foldl
    (·.insert ·) {}
  let packed (f : FilePath) := fresh.contains (f.toString.drop (pkg.leanLibDir.toString.length + 1)).toString
  let changed ← names.filterM fun m => do
    let some mod := pkg.findModule? m.toName | return true
    if !packed mod.oleanFile then return true
    (Lean.PaperLean.moduleFiles mod.oleanFile).anyM fun f => return !packed f && (← f.pathExists)
  let out : Std.HashSet String := changed.foldl (·.insert ·) {}
  return { lib with
    interpreted := lib.interpreted.filter (!out.contains ·.1)
    importers := lib.importers.filter (!out.contains ·)
    plugin := lib.plugin.filter (!out.contains ·.1)
    outdated := lib.outdated ++ changed }

/-- A digest of what `prepare` goes by for `pkg` besides its modules' files, which what it finds holds only
with: the compiler, and of `pkg` and the packages it depends on, whose libraries its own uses, the default
targets, and of each library what it compiles and links with and whether it loads as a plugin. -/
public def packageConfig (lean : LeanInstall) (pkg : Package) : String :=
  let ofPackage (p : Package) : UInt64 :=
    p.leanLibs.foldl (init := mixHash (hash p.baseName) (hash p.defaultTargets)) fun h lib =>
      mixHash h <| hash (lib.name, lib.shouldPrecompile, lib.weakLeancArgs, lib.leancArgs,
        lib.weakLinkArgs, lib.linkArgs)
  let compiler := hash (lean.cc.toString, lean.ccFlags, lean.ccLinkFlags true)
  toString <| (closurePackages pkg).foldl (mixHash · <| ofPackage ·) (mixHash compiler (ofPackage pkg))

/-- Whether `l` was prepared with the configuration that its package has in `ws`. -/
def configCurrent (ws : Workspace) (l : PreparedNative) : Bool :=
  (ws.packages.find? (pkgKey · == l.pkg)).any (packageConfig ws.lakeEnv.lean · == l.config)

/-- `l`, with what was found of its modules only if `configCurrent`: a change of the configuration leaves
all of their files as they are. -/
public def currentFindings (ws : Workspace) (l : PreparedNative) : PreparedNative :=
  if configCurrent ws l then l else
  { l with
    interpreted := #[], importers := #[], plugin := #[], others := #[]
    outdated := l.outdated ++ l.interpreted.map (·.1) ++ l.importers ++ l.plugin.map (·.1) ++ l.others }

/-- A digest of the modules of the default libraries of `pkg` and of the files of each, which why its
library could not be built holds only for, as for `packageConfig`. -/
public def nativeInputs (pkg : Package) : IO String := do
  let mut h : UInt64 := 7
  for mod in ← libraryModules pkg do
    h := mixHash h (hash mod.name)
    for f in Lean.PaperLean.moduleFiles mod.oleanFile ++ #[mod.cFile, mod.traceFile] do
      h := mixHash h (hash (← Lean.PaperLean.fileIdentity f.toString))
  return toString h

/-- `summary`, of prepared data with the libraries `libs`, saying of a package what it found only if that
still holds: why it has no native library if it would try the same now (`nativeInputs`), and what
its library leaves out if `configCurrent`. How many modules a library holds does not change. -/
public def currentSummary (ws : Workspace) (libs : Array PreparedNative) (summary : Array String) :
    IO (Array String) := do
  let mut out := summary
  for l in libs do
    let same ← match ws.packages.find? (pkgKey · == l.pkg) with
      | some pkg =>
        if !configCurrent ws l then pure false
        else if !l.failed then pure true
        else try pure ((← nativeInputs pkg) == l.inputs) catch _ => pure false
      | none => pure false
    unless same do
      -- (as `pkgKey` is a package's name)
      let start := s!"{l.pkg}: "
      let now := if l.failed then "not built (its files or configuration may have changed since it failed)"
        else s!"{l.modules} modules (its configuration or a dependency's may have changed since)"
      out := out.map fun line => if line.startsWith start then start ++ now else line
  return out

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
    let oldLibs := old?.map (·.libs) |>.getD #[]
    let mut packs : Array String := #[]
    let mut image? : Option String := none
    let mut libs : Array PreparedNative := #[]
    let mut summary : Array String := #[]
    let mut failed : Array String := #[]
    let mut pluginCode : NameSet := {}
    if keepDeps then
      if let some old := old? then
        packs := old.packs.filter (!·.startsWith "root-")
        image? := old.image?
        libs := oldLibs
        summary := old.summary
    else if !deps.isEmpty then
      IO.FS.createDirAll depDir
      -- The dependency pack, written while the native libraries compile, and its import image, written
      -- after them, as the program that writes it imports all dependency modules, which takes much
      -- memory.
      let pack : IO Unit := do
        let start ← IO.monoMsNow
        IO.println s!"Packing {deps.size} dependency packages and Lean's library..."
        let n ← Lean.PaperLean.OLeanPack.create depRoots (depDir / "deps.paperlean") (storedRoots := stored depRoots)
          (keep := ← currentArtifact deps)
        IO.println s!"  {n} files ({showTime ((← IO.monoMsNow) - start)})"
      let writeImage : IO (Option String) := do
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
          -- (the last line: packages' initializers may print too)
          IO.println s!"  {((out.stdout.dropEndWhile Char.isWhitespace).toString.splitOn "\n").getLast!} entries \
            ({showTime ((← IO.monoMsNow) - start)})"
          return some s!"{depDirName}/deps.image.paperlean"
        else
          IO.eprintln s!"paperlean: warning: no import image, as writing it failed:\n{out.stderr}"
          return none
      let packTask ← IO.asTask pack .dedicated
      -- Native libraries, dependencies first: built for the packages of `built`, kept for the others
      -- (whose libraries, and those they are linked against, are as they were). A package is skipped
      -- if its library cannot be built or one that it depends on has none. The units of modules of
      -- all of them compile on `jobs` workers, each taking the next unit, and a library is linked when
      -- its units are compiled.
      let jobs ← if opts.jobs > 0 then pure opts.jobs else autoJobs
      let lean := ws.lakeEnv.lean
      let needsOf (pkg : Package) := (closure pkg).map (·.toString (escape := false))
      -- (not those that need a library that is neither built nor kept)
      let toBuild := if !native then #[] else deps.filter fun pkg =>
        built.contains (pkgKey pkg) && (needsOf pkg).all fun d => !deps.any (pkgKey · == d) ||
          built.contains d || oldLibs.any (fun l => l.pkg == d && !l.failed)
      -- (first: what changes while it is built then shows as something else)
      let (inputs, plans) ← try
          let tried := if native then deps.filter (built.contains <| pkgKey ·) else #[]
          let inputs ← tried.foldlM (init := ({} : Std.HashMap String String)) fun m pkg =>
            return m.insert (pkgKey pkg) (← nativeInputs pkg)
          pure (inputs, ← toBuild.mapM fun pkg => planNativeLib lean pkg jobs)
        catch e => let _ ← IO.wait packTask; throw e
      let units := plans.mapIdx (fun i p => p.units.map fun (a, b) => (i, a, b)) |>.flatten
      -- per package, its plan, the results of its units, the number of those not done yet, and
      -- whether they need not be compiled, as the package is skipped
      let states ← plans.mapM fun p =>
        return (p, ← IO.mkRef (#[] : Array ModuleResult), ← IO.mkRef p.units.size, ← IO.mkRef false)
      let total := plans.foldl (· + ·.modules.size) 0
      for p in plans do
        IO.println s!"Compiling the native library of {p.pkg.prettyName} ({jobs} jobs, {p.units.size} units)..."
      let startCompile ← IO.monoMsNow
      -- (of all dependency packages, whose code calls one another's; after the pack, whose writer
      -- needs its address range, where reading `.olean` files maps them)
      let verdictsTask ← IO.mapTask (t := packTask) (prio := .dedicated) fun _ => do
        if plans.isEmpty then return ({} : Lean.PaperLean.EvalVerdicts)
        let tmp := depDir / "tmp-eval"
        let start ← IO.monoMsNow
        let verdicts ← evalImpurities ws deps (depDir / "deps.paperlean") tmp
        IO.FS.removeDirAll tmp
        IO.println s!"  evaluated the packages' constants ({showTime ((← IO.monoMsNow) - start)})"
        return verdicts
      let done ← IO.mkRef 0
      let last ← IO.mkRef 0
      let progress (n : Nat) : BaseIO Unit := do
        let d ← done.modifyGet fun d => (d + n, d + n)
        let now ← IO.monoMsNow
        if d == total || now - (← last.modifyGet fun l => (l, if now - l ≥ 5000 then now else l)) ≥ 5000 then
          let eta := if d == 0 || d == total then "" else
            s!", about {showTime ((now - startCompile) * (total - d) / d)} left"
          (IO.println s!"  {d} of {total} modules{eta}").catchExceptions fun _ => pure ()
      let next ← IO.mkRef 0
      let worker : BaseIO Unit := do
        repeat
          let u ← next.modifyGet fun u => (u, u + 1)
          let some (i, a, b) := units[u]? | break
          let some (plan, results, remaining, skipped) := states[i]? | continue
          unless ← skipped.get do
            let r ← compileNativeUnit lean (dir / nativeDirName) plan a b
            results.modify (· ++ r)
          remaining.modify (· - 1)
          progress (b - a)
      let workers ← (List.range jobs).mapM fun _ => BaseIO.asTask worker .dedicated
      -- the units of the packages that need `key`'s library need not be compiled
      let skipDependents (key : String) : BaseIO Unit := do
        for pkg in toBuild, (_, _, _, skipped) in states do
          if (needsOf pkg).contains key then skipped.set true
      -- (on an error, after the workers and the pack and image are done with the directories)
      let finish : LoggerIO Unit := do
        for w in workers do
          let _ ← IO.wait w
        let _ ← IO.wait packTask
        let _ ← IO.wait verdictsTask
      try
        for pkg in deps do
          let key := pkgKey pkg
          for m in ← pluginModules pkg do pluginCode := pluginCode.insert m
          unless built.contains key do
            if let some lib := oldLibs.find? (·.pkg == key) then
              libs := libs.push lib
              if let some line := old?.bind fun old => old.summary.find? (·.startsWith s!"{pkg.prettyName}: ") then
                summary := summary.push line
            continue
          unless native do continue
          let needs := needsOf pkg
          if let some dep := needs.find? fun d => deps.any (pkgKey · == d) && !libs.any (fun l => l.pkg == d && !l.failed) then
            IO.eprintln s!"paperlean: skipping the native library of {pkg.prettyName}: {dep} has none"
            summary := summary.push s!"{pkg.prettyName}: not built ({dep} has no native library)"
            failed := failed.push pkg.prettyName
            libs := libs.push { pkg := key, manifest := "", lib := "", modules := 0, failed := true,
                                inputs := inputs.getD key "" }
            skipDependents key
            continue
          let some (plan, results, remaining, _) := (toBuild.findIdx? (pkgKey · == key)).bind (states[·]?) | continue
          while (← remaining.get) > 0 do
            IO.sleep 20
          let depLibs : Array NativeLib := libs.filter (fun l => needs.contains l.pkg && l.modules > 0) |>.map fun l =>
            { pkg := l.pkg.toName, lib := dir / l.lib, manifest := dir / l.manifest, modules := l.modules, excluded := #[] }
          let verdicts ← IO.ofExcept (← IO.wait verdictsTask)
          let (lib?, log) ← (finishNativeLib ws plan (← results.get) depLibs (dir / nativeDirName) jobs verdicts).captureLog
          log.replay
          let some lib := lib?
            | -- the first line of the error, for the summary and `status`
              let why := (log.entries.find? (·.level == .error)).map (·.message.splitOn "\n" |>.head!) |>.getD "error"
              IO.eprintln s!"paperlean: the native library of {pkg.prettyName} could not be built (the error above)"
              summary := summary.push s!"{pkg.prettyName}: not built ({why})"
              failed := failed.push pkg.prettyName
              libs := libs.push { pkg := key, manifest := "", lib := "", modules := 0, failed := true,
                                  inputs := inputs.getD key "" }
              skipDependents key
          -- (built modules that are not in the plan: what the root package imports of them is said
          -- here, what something else may import by the import)
          let imported := depMods.foldl (·.insert ·.name) ({} : NameSet)
          let (outside, others) := plan.others.partition (imported.contains ·.name)
          -- (what a library does not use is interpreted, unless Lake loads its code as a plugin, which
          -- the loader then uses as Lean does; a module that it holds no code of is not its concern)
          let isPlugin (m : Name) := (pkg.findModule? m).any (·.lib.shouldPrecompile)
          pluginCode := lib.excluded.foldl (·.erase ·.1) pluginCode
          let others := others.filter (!isPlugin ·.name)
          let (rejected, left) := (lib.excluded ++ outside.map (·.name, "it is in no default library of its \
            package")).partition (isPlugin ·.1)
          let (rejected', own) := lib.interpreted.partition (isPlugin ·.1)
          let plugin := rejected ++ rejected'
          let below := left ++ own
          if lib.modules == 0 && below.isEmpty && others.isEmpty && plugin.isEmpty then
            libs := libs.push { pkg := key, manifest := "", lib := "", modules := 0 }
            IO.println s!"  {pkg.prettyName}: no built modules"
            continue
          -- (dependencies come first, so that their importers are among these)
          let interpreted := libs.foldl (init := below.foldl (·.insert ·.1) ({} : NameSet)) fun s l =>
            ((l.importers ++ l.others ++ l.outdated).foldl (·.insert ·.toName)
              (l.interpreted.foldl (·.insert ·.1.toName) s))
          let scanned := (plan.modules ++ outside).filter (!isPlugin ·.name)
          let importers ← importersIn scanned (others.foldl (·.insert ·.name) interpreted)
          -- (a library's code that calls a plugin's would call its own copy: `native_libs.cpp`)
          let onPlugin := (← importersIn scanned pluginCode).filter fun m =>
            !importers.contains m && !interpreted.contains m
          libs := libs.push {
            pkg := key, modules := lib.modules
            manifest := if lib.modules == 0 then "" else s!"{nativeDirName}/{lib.manifest.fileName.getD ""}"
            lib := if lib.modules == 0 then "" else s!"{nativeDirName}/{lib.lib.fileName.getD ""}"
            interpreted := (below.map fun (m, why) => (m.toString, why)) ++
              onPlugin.map (·.toString, "it imports a module whose native code a plugin loaded, so its \
                library's code is not used")
            importers := importers.map toString
            plugin := plugin.map fun (m, why) => (m.toString, why)
            others := others.map (·.name.toString) }
          let count := own.size + onPlugin.size + importers.size
          let excl := (if left.isEmpty then "" else s!", {left.size} left out") ++
            (if count == 0 then "" else s!", {count} interpreted unless a plugin loads them") ++
            (if plugin.isEmpty then "" else s!", {plugin.size} rejected, whose code a plugin loads") ++
            (if others.isEmpty then "" else s!", {others.size} outside its default libraries")
          summary := summary.push s!"{pkg.prettyName}: {lib.modules} modules{excl}"
          IO.println s!"  {pkg.prettyName}: {lib.modules} modules{excl} ({showTime ((← IO.monoMsNow) - startCompile)})"
          for (m, why) in left.toSubarray 0 5 ++ own.toSubarray 0 5 ++ plugin.toSubarray 0 5 do
            IO.println s!"  e.g. {m}: {why}"
          if h : importers.size > 0 then
            IO.println s!"  e.g. {importers[0]}: it imports one of them"
      catch e =>
        for (_, _, _, skipped) in states do skipped.set true
        finish
        throw e
      finish
      IO.ofExcept (← IO.wait packTask)
      packs := #[s!"{depDirName}/deps.paperlean"]
      -- What the libraries that stay say is of the old pack's files. (Compared after the new pack is
      -- written: a file that has the identity of the old pack's now had it then.)
      if let some oldPack := old?.bind (·.packs.find? (·.endsWith "/deps.paperlean")) then
        for pkg in deps do
          unless built.contains (pkgKey pkg) do
            libs ← libs.mapM fun l => if l.pkg == pkgKey pkg then keptFindings pkg (dir / oldPack) l else pure l
      image? ← writeImage
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
    -- (one that stays holds for the configuration that it was prepared with)
    libs := libs.map fun l =>
      if built.contains l.pkg then
        { l with config := ((ws.packages.find? (pkgKey · == l.pkg)).map (packageConfig ws.lakeEnv.lean)).getD "" }
      else currentFindings ws l
    summary ← currentSummary ws libs summary
    -- (a library that a failed one's dependents would need is never used, so it is not listed)
    let usable := libs.filter fun l => l.modules > 0 && !l.failed
    let data : PreparedData := {
      paperlean := Lean.PaperLean.version, build? := some Lean.PaperLean.build, githash := Lean.githash
      platform := System.Platform.target
      packs, image?, summary
      native := usable.map (·.manifest)
      packages := deps.map pkgKey
      libs }
    data.install dir
    -- the directories that `env.json` no longer refers to, and the packs of interrupted builds
    let used := packs ++ image?.toArray ++ usable.map (·.manifest) ++ usable.map (·.lib)
    for e in ← dir.readDir do
      if (isDataDirName e.fileName || e.fileName == "tmp") &&
          !used.any (·.startsWith (e.fileName ++ "/")) then
        removePath e.path
    BuildData.removeEnded ws.dir
    IO.println s!"Prepared {dir}."
    unless failed.isEmpty do
      IO.eprintln s!"paperlean: warning: no native library for {", ".intercalate failed.toList} (see above), \
        so their code runs in the interpreter where no plugin loads it: the same results, but slower. \
        `paperlean status` shows this too."
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
  let free ← availableSpace dir
  if need + need / 10 > free then
    IO.eprintln s!"paperlean: {what} needs about {showBytes (need + need / 10)} of disk space in {dir}, \
      but only {showBytes free} are free. Nothing was changed."
    return false
  return true

/-- A stamp for the names of the directories that a run writes in the data directory `dir`: the
monotonic clock in milliseconds, which starts again after a reboot, so made unique there. -/
def freshStamp (dir : FilePath) : IO String := do
  let mut n ← IO.monoMsNow
  while ← ["deps-", "native-", "root-"].anyM fun p => (dir / s!"{p}{n}").pathExists do
    n := n + 1
  return toString n

/-- Runs `act` holding the lock of the prepared data in `dir` if `env.json` is still `text?`, which
the command read before: otherwise another command changed it meanwhile, and nothing is done. -/
def withUnchangedData (ws : Workspace) (text? : Option (Except String String)) (act : LoggerIO UInt32) :
    LoggerIO UInt32 :=
  withDataLock (dataDir ws.dir) do
    let same := match ← preparedDataText ws.dir, text? with
      | none, none => true
      | some (.ok a), some (.ok b) | some (.error a), some (.error b) => a == b
      | _, _ => false
    unless same do
      IO.eprintln "paperlean: another paperlean command changed the prepared data meanwhile; run the \
        command again. Nothing was changed."
      return 1
    act

/-- After the run `stamp` of `prepareIn` or `refresh` failed: deletes what it wrote in `dir` (its
directories, and the files `files` relative to `dir`), unless `env.json` already refers to it (the
failure came after it was written). The data that an older `env.json` refers to is untouched. -/
def removeFailedRun (ws : Workspace) (dir : FilePath) (stamp : String) (files : Array String := #[]) :
    IO Unit := do
  let used := match ← readPreparedData ws.dir with
    | some (.ok d) => d.packs ++ d.image?.toArray ++ d.native
    | _ => #[]
  for d in [s!"deps-{stamp}", s!"native-{stamp}", s!"root-{stamp}"] do
    if !used.any (·.startsWith (d ++ "/")) then removePath (dir / d)
  for f in files do
    if !used.contains f then BuildData.removePack (dir / f)

/-- Deletes a file in place of the data directory `dir`, which only damage puts there. -/
def removeFileAtDataDir (dir : FilePath) : IO Unit := do
  if (← dir.pathExists) && !(← dir.isDir) then IO.FS.removeFile dir

/-- Prepares the data of `ws`; the exit code. -/
public def prepare (ws : Workspace) (opts : PrepareOptions) : LoggerIO UInt32 := do
  let dir := dataDir ws.dir
  removeFileAtDataDir dir
  let allDeps := dependencies ws
  let leanLib := ws.lakeEnv.lean.leanLibDir
  let text? ← preparedDataText ws.dir
  let old? : Option PreparedData := match parsePreparedData ws.dir text? with
    | some (.ok d) => if d.mismatch?.isNone then some d else none
    | _ => none
  let before := old?.map (·.packages) |>.getD #[]
  let (deps, built) := plan allDeps before (old?.map (·.libs) |>.getD #[]) opts.packages opts.root
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
    let stamp ← freshStamp dir
    try prepareIn ws opts dir stamp deps built keepDeps depRoots depMods rootMods rootUnbuilt native old?
    catch e => removeFailedRun ws dir stamp; throw e

/-- What `paperlean clean` of named packages says if it found `env.json` damaged (`why`) and reset it
(`PreparedData.empty`): none of its paths is trusted, so the files of the data stay. -/
public def damagedNote (why : String) : String :=
  s!"The prepared data was not usable: {why}. It is reset, so nothing is prepared now; its files stay \
    until `paperlean prepare` replaces them or `paperlean clean` deletes them."

/-- `paperlean clean` of the dependency packages `pkgs`: deletes their prepared data and that of the
prepared packages that depend on them. The others keep theirs: the dependency pack and its image are
written again without them, and their native libraries stay. -/
public def cleanPackages (ws : Workspace) (pkgs : Array Package) : LoggerIO UInt32 := do
  let dir := dataDir ws.dir
  let text? ← preparedDataText ws.dir
  let data? := parsePreparedData ws.dir text?
  if let some (.error e) := data? then
    return ← withUnchangedData ws text? do
      PreparedData.empty.install dir
      IO.println (damagedNote e)
      return 0
  let some (.ok old) := data?
    | IO.println "There is no prepared data."; return 0
  if let some why := old.mismatch? then
    IO.eprintln s!"paperlean: the prepared data cannot be used ({why}); `paperlean clean` deletes all of \
      it. Nothing was deleted."
    return 1
  let allDeps := dependencies ws
  let before := old.packages
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
    let stamp ← freshStamp dir
    try prepareIn ws {} dir stamp deps #[] false depRoots depMods 0 0 false (some old)
    catch e => removeFailedRun ws dir stamp; throw e
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

/-- Whether `p` is a path of a pack of the root package's changes as `refresh` writes it:
`root-<n>/changes-<m>.delta.paperlean`. -/
def isDeltaPath (p : String) : Bool :=
  match p.splitOn "/" with
  | [d, f] => d.startsWith "root-" && isDataDirName d &&
    ((f.dropPrefix? "changes-").bind (·.dropSuffix? ".delta.paperlean")).any fun n =>
      !n.isEmpty && n.all Char.isDigit
  | _ => false

/-- Deletes the packs of changes in the directory of the root package's pack `base` that `packs`
does not list, which interrupted runs of `refresh` left, and their temporary files. -/
def removeLeftDeltas (dir : FilePath) (base : String) (packs : Array String) : IO Unit := do
  let d := (base.splitOn "/").headD ""
  let .ok entries ← (dir / d).readDir.toBaseIO | return
  for e in entries do
    let p := s!"{d}/{e.fileName}"
    match p.splitOn ".tmp." with
    | [pack, pid] =>
      if isDeltaPath pack then
        if let some pid := pid.toNat? then
          unless ← Lean.PaperLean.processAlive pid.toUInt32 do removePath e.path
    | _ => if isDeltaPath p && !packs.contains p then BuildData.removePack e.path

/-- `paperlean build --prepare`: packs the files of the root package's current modules that its
pack does not serve, as they changed or were added since it was written, into a pack of their own
that replaces the previous one; the root package's pack itself is not rewritten. Writes the root
package's pack if it has none, and prepares everything if nothing is prepared. -/
public def refresh (ws : Workspace) : LoggerIO UInt32 := do
  let dir := dataDir ws.dir
  removeFileAtDataDir dir
  let text? ← preparedDataText ws.dir
  let data? := parsePreparedData ws.dir text?
  if let some (.error e) := data? then
    IO.println s!"The prepared data cannot be used ({e}); preparing everything."
    return ← prepare ws { root := true }
  let some (.ok d) := data?
    | IO.println "Nothing is prepared yet; preparing everything."
      prepare ws { root := true }
  if let some why := d.mismatch? then
    IO.println s!"The prepared data cannot be used ({why}); preparing everything."
    return ← prepare ws { root := true }
  if d.isEmpty then
    IO.println "Nothing is prepared yet; preparing everything."
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
  unless ← enoughSpace dir need "packing the changed modules" do return 1
  withUnchangedData ws text? do
    let stamp ← freshStamp dir
    let newDelta? := base?.map fun base => s!"{(base : FilePath).parent.get!}/changes-{stamp}.delta.paperlean"
    try
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
            let rel := newDelta?.get!
            let n ← Lean.PaperLean.OLeanPack.create #[root] (dir / rel) rootDeltaBase
              (storedRootsFor ws #[root]) keep
            IO.println s!"Packed {n} files of the {stale} of {total} modules of {ws.root.prettyName} that \
              changed or were added since its pack was written ({showTime ((← IO.monoMsNow) - start)})."
            if 2 * stale > total then
              IO.println s!"(`paperlean prepare {ws.root.prettyName}` packs them all again, which reads a \
                little faster.)"
            -- before the root package's pack, so that it serves the files that changed
            pure (some rel, others.flatMap fun p => if some p == base? then #[rel, p] else #[p])
      ({ d with packs } : PreparedData).install dir
      if let some old := delta? then
        if some old != file? && isDeltaPath old then BuildData.removePack (dir / old)
      if let some base := base? then removeLeftDeltas dir base packs
      return 0
    catch e => removeFailedRun ws dir stamp newDelta?.toArray; throw e

end Lake.PaperLean
