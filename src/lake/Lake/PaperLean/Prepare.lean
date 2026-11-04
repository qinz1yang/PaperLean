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
import Lake.PaperLean.Cache
import Lean.PaperLean.OLeanPack
import Lean.PaperLean.System
import Std.Data.HashMap
import Lean.Data.NameMap
import Lean.Elab.ParseImportsFast
import Init.Data.ByteArray.Extra

/-!
`paperlean prepare`: writes a workspace's prepared data (`Lake.PaperLean.Env`). Per dependency package,
a pack of its files and its native library are entries of the cache that the workspaces of a user
share (`Lake.PaperLean.Cache`), keyed by the content hashes of the files that they are made of
(`packKey`, `nativeKey`), which a record of the workspace keeps (`OLeanPack.hashFiles`), so that a file
is read again only once it changed: `prepare` writes only the entries that are missing, and compiles
only the units of a library whose objects are missing. The workspace reads a pack through a binding of
its own (`OLeanPack.bind`), which serves a packed file only while the workspace's file has the identity
that it had when its content hash was found to be that of the packed file; any other file is read from
disk, so that what Lean reads does not depend on the cache. The pack of Lean's library is shared
likewise (`BuildData.toolchainPack`). The import image of these packs is the workspace's own, and so is
the pack of the root package, if asked for. Each run writes new files (`bind/`, `image-<stamp>/`,
`root-<stamp>/`) and then replaces `env.json`, so that an interrupted run leaves the old data intact;
the next run deletes what `env.json` does not refer to.
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

/-- A parsed source header, reusable only while its file keeps its full identity. Name components
are stored separately so that escaped dots in module names round-trip. -/
structure ImportHeader where
  path : String
  identity : Array UInt64
  imports : Array (Array String)
  deriving ToJson, FromJson

structure ImportHeaders where
  entries : Std.HashMap String ImportHeader := {}
  changed : Bool := false

/-- The workspace's parsed source headers. Damaged data or data from another build is ignored. -/
def readImportHeaders (ws : Workspace) : IO (IO.Ref ImportHeaders) := do
  try
    let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile (dataDir ws.dir / "imports.paperlean"))
    let (build, digest, entries) : String × String × Array ImportHeader ← IO.ofExcept (fromJson? json)
    if build != Cache.buildName || digest != Cache.key #[build, (toJson entries).compress] then
      return ← IO.mkRef {}
    return ← IO.mkRef { entries := entries.foldl (fun m e => m.insert e.path e) {} }
  catch _ => IO.mkRef {}

/-- Saves newly parsed headers only after a successful prepare, holding its data lock. -/
def writeImportHeaders (dir : FilePath) (headers : IO.Ref ImportHeaders) : IO Unit := do
  let headers ← headers.get
  unless headers.changed do return
  let entries := headers.entries.toArray.map (·.2) |>.qsort (·.path < ·.path)
  let build := Cache.buildName
  let digest := Cache.key #[build, (toJson entries).compress]
  let tmp := dir / s!"imports.paperlean.tmp.{← IO.Process.getPID}"
  try
    IO.FS.writeFile tmp ((toJson (build, digest, entries)).compress ++ "\n")
    IO.FS.rename tmp (dir / "imports.paperlean")
  finally
    try IO.FS.removeFile tmp catch _ => pure ()

/-- The source's direct imports, using a cached header only for the same file identity. -/
def sourceImports (headers : IO.Ref ImportHeaders) (mod : Module) : IO (Array Name) := do
  let path := mod.leanFile.toString
  let before ← Lean.PaperLean.fileIdentity path
  let identity := before.map fun id =>
    (Array.range (id.size / 8)).map fun i => (id.extract (8 * i) (8 * (i + 1))).toUInt64LE!
  if let some identity := identity then
    if let some entry := (← headers.get).entries[path]? then
      if entry.identity == identity then
        return entry.imports.map fun parts => parts.foldl Name.mkStr .anonymous
  unless ← mod.leanFile.pathExists do return #[]
  let some header ← (some <$> Lean.parseImports' (← IO.FS.readFile mod.leanFile) path)
    <|> pure none | return #[]
  let imports := header.imports.map (·.module)
  if let some identity := identity then
    if before == (← Lean.PaperLean.fileIdentity path) then
      let names := imports.map fun n => n.components.toArray.map Name.getString!
      let entry : ImportHeader := { path, identity, imports := names }
      headers.modify fun h => { h with entries := h.entries.insert path entry, changed := true }
  return imports

/-- The dependency modules in the root package's import closure, using parsed source headers. -/
partial def importedDependencyModulesWith (ws : Workspace) (headers : IO.Ref ImportHeaders) :
    IO (Array Module) := do
  let mut todo ← defaultModules ws.root
  let mut seen : NameSet := todo.foldl (·.insert ·.name) {}
  let mut out := #[]
  while h : todo.size > 0 do
    let mod := todo.back
    todo := todo.pop
    if mod.pkg.baseName != ws.root.baseName then out := out.push mod
    for imp in ← sourceImports headers mod do
      -- Lean's own modules are not in the workspace
      if let some dep := ws.findModule? imp then
        unless seen.contains dep.name do
          seen := seen.insert dep.name
          todo := todo.push dep
  return out

/-- The modules of the dependency packages that the root package's modules import directly or
indirectly, by their sources' headers (as Lake reads them; a header that cannot be parsed is
skipped, as `lake build` reports it). -/
public def importedDependencyModules (ws : Workspace) : IO (Array Module) := do
  importedDependencyModulesWith ws (← readImportHeaders ws)

/-- Those of `modules` that import one of `below` directly or indirectly, leaving out `below`: a
module runs in the interpreter if one of its imports does. By their sources' headers. -/
def importersIn (headers : IO.Ref ImportHeaders) (modules : Array Module) (below : NameSet) :
    IO (Array Name) := do
  if below.isEmpty then return #[]
  let mut mods : Array (Name × Array Name) := #[]
  for mod in modules do
    mods := mods.push (mod.name, ← sourceImports headers mod)
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
(dependencies first), and those whose data it prepares now, from the files they have now; the others
keep theirs. Without names (`named`), all dependency packages, all prepared now. With names, the named
packages and the packages they depend on (with `root`, all dependency packages), and the packages
prepared before (`before`); those prepared now are the named packages, the packages without a library
in `libs` and those that depend on a package prepared now. -/
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

/-- The address at which the root package's pack is mapped, disjoint from the other packs'. -/
def rootPackBase : USize := 0x240000000000

/-- The Lean program that writes an import image (`Lean.PaperLean.writeImportImage`) of the packs in
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

/-- `lib`, the native library of `pkg` that prepared data keeps, with what was found of its modules
only for those whose files are still those of `oldPack`, the pack (or binding) that it holds for: the
others are `outdated`. A module that did not change and imports one that runs in the interpreter still
does: the libraries of the packages it depends on stay too, so that nothing gives the module that it
imports native code. -/
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

/-- The files of `pkg` that its pack holds: those below its library directory of the current modules
that packs hold (`currentArtifact`), sorted. -/
def packableFiles (pkg : Package) (current : String → IO Bool) : IO (Array String) := do
  unless ← pkg.leanLibDir.isDir do return #[]
  let exts := #[".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir"]
  let mut out := #[]
  for p in ← pkg.leanLibDir.walkDir do
    let f := p.toString
    if exts.any (f.endsWith ·) && (← current f) then out := out.push f
  return out.qsort (· < ·)

/-- The size of the file whose identity (`Lean.PaperLean.fileIdentity`) is `id`. -/
def identitySize (id : ByteArray) : Nat := (id.extract 16 24).toUInt64LE!.toNat

/-- The key of the pack of `pkg` that holds `files`, of its library directory: of the package's name
and the files' paths in the directory and content hashes. -/
def packKey (pkg : Package) (files : Array String) (hashes : FileHashes) : String :=
  let n := pkg.leanLibDir.toString.length + 1
  Cache.key <| #["pack", pkgKey pkg] ++ files.map fun f => s!"{f.drop n}\t{(hashes.getD f default).2}"

/-- The key of the native library of `pkg` with the library modules `mods` and the other built
modules `others`, whose pack has the key `pack`: of the pack, the `.c` files of `mods`, the compiler
and the configuration (`packageConfig`), the variables that change how it is built for tests, and the
entries of the libraries of the packages that it depends on (`deps`: of each, the entry, or why it has
none). -/
def nativeKey (lean : LeanInstall) (pkg : Package) (pack : String) (mods others : Array Module)
    (hashes : FileHashes) (deps : Array String) : IO String := do
  let vars ← #["PAPERLEAN_EVAL_SECONDS", "PAPERLEAN_EVAL_MEMORY", "PAPERLEAN_UNIT_BYTES"].mapM fun v =>
    return s!"{v}={(← IO.getEnv v).getD ""}"
  return Cache.key <| #["native", pack, packageConfig lean pkg] ++ vars ++
    mods.map (fun m => s!"{m.name}\t{(hashes.getD m.cFile.toString default).2}") ++
    others.map (s!"other\t{·.name}") ++ deps

/-- What a native entry of the cache records besides its files (`native.json`): the library, whose
`interpreted` a workspace's data fills in (`nativeView`) from the modules left out of it and those that
it holds that run in the interpreter, of its default libraries (`left`, `own`), and from those that
import a module whose native code a plugin loads (`onPlugin`); and all modules left out of it. -/
structure NativeEntry where
  lib : PreparedNative
  left : Array (String × String)
  own : Array (String × String)
  onPlugin : Array String
  excluded : Array String
  deriving ToJson, FromJson

/-- What the prepared data of a workspace whose root package imports the modules `imported` lists of
the native entry `n` of `pkg`, its line of the summary, and the modules left out: of the modules in no
default library, those that it imports count as left out. -/
def nativeView (pkg : Package) (n : NativeEntry) (imported : NameSet) :
    PreparedNative × String × Array (String × String) :=
  let (outside, others) := n.lib.others.partition (imported.contains ·.toName)
  let left := n.left ++ outside.map (·, "it is in no default library of its package")
  let onPlugin := n.onPlugin.filter (!n.lib.others.contains ·)
  let lib := { n.lib with
    others
    interpreted := left ++ n.own ++ onPlugin.map (·, "it imports a module whose native code a plugin \
      loaded, so its library's code is not used") }
  let count := n.own.size + onPlugin.size + lib.importers.size
  let excl := (if left.isEmpty then "" else s!", {left.size} left out") ++
    (if count == 0 then "" else s!", {count} interpreted unless a plugin loads them") ++
    (if lib.plugin.isEmpty then "" else s!", {lib.plugin.size} rejected, whose code a plugin loads") ++
    (if others.isEmpty then "" else s!", {others.size} outside its default libraries")
  (lib, s!"{pkg.prettyName}: {lib.modules} modules{excl}", left)

/-- The native entry `entry` of `cdir`, if it is there. -/
def readNativeEntry (cdir : FilePath) (entry : String) : IO (Option NativeEntry) := do
  let file := cdir / entry / "native.json"
  unless ← file.pathExists do return none
  return (Json.parse (← IO.FS.readFile file) >>= fromJson?).toOption

/-- Prints examples of the modules of the native entry `n` that run in the interpreter, of which those
of `left` are left out of it. -/
def examples (left : Array (String × String)) (n : NativeEntry) : IO Unit := do
  for (m, why) in left.toSubarray 0 5 ++ n.own.toSubarray 0 5 ++ n.lib.plugin.toSubarray 0 5 do
    IO.println s!"  e.g. {m}: {why}"
  if h : n.lib.importers.size > 0 then
    IO.println s!"  e.g. {n.lib.importers[0]}: it imports one of them"

/-- The cache directory for `ws` (`Cache.root?`), or, if the user has none, one in the data directory. -/
def cacheRootOf (ws : Workspace) : IO FilePath := do
  let root ← match ← Cache.root? with
    | some r => pure r
    | none => pure (dataDir ws.dir / "cache")
  IO.FS.createDirAll root
  IO.FS.realPath root

/-- The packs of the dependency packages and of Lean's library in the data directory `dir`, as
`LEAN_OLEAN_PACK` lists them for the processes that `prepare` runs. -/
def depPacks (dir cacheRoot : FilePath) (deps : Array PreparedPackage) (toolchain? : Option String) :
    String :=
  ":".intercalate ((deps.filter (!·.binding.isEmpty)).map (dir / ·.binding |>.toString) ++
    toolchain?.toArray.map fun (t : String) => (cacheRoot / t).toString).toList

/-- The modules of `deps` whose files the import image describes: those that the root package's
modules import (all of the packages' modules if they import none). -/
def imageModules (ws : Workspace) (deps : Array Package) (headers : IO.Ref ImportHeaders) :
    IO (Array Module × Array Module) := do
  let imported := (← importedDependencyModulesWith ws headers).filter fun m => deps.any (·.baseName == m.pkg.baseName)
  let candidates ← if imported.isEmpty then (deps.flatMapM defaultModules : IO (Array Module)) else pure imported
  return (imported, candidates)

/-- Whether `need` bytes fit into the free space of `dir`; says why not if not. -/
def enoughSpace (dir : FilePath) (need : Nat) (what : String) : IO Bool := do
  IO.FS.createDirAll dir
  let free ← availableSpace dir
  if need + need / 10 > free then
    IO.eprintln s!"paperlean: {what} needs about {showBytes (need + need / 10)} of disk space in {dir}, \
      but only {showBytes free} are free. Nothing was changed."
    return false
  return true

/-- Writes into `image-<stamp>/` of the data directory `dir` the import image of the packs `packs`
(`LEAN_OLEAN_PACK`), after importing the modules `mods`; the image, relative to `dir`, or `none` if
it cannot be written. -/
def writeImage (ws : Workspace) (dir : FilePath) (stamp : String) (mods : Array Module) (packs : String) :
    IO (Option String) := do
  let start ← IO.monoMsNow
  IO.println s!"Writing the import image of {mods.size} modules..."
  let name := s!"image-{stamp}"
  let tmp := dir / name / "tmp"
  IO.FS.createDirAll tmp
  IO.FS.writeFile (tmp / "Image.lean") imageProgram
  IO.FS.writeFile (tmp / "modules.txt") ("\n".intercalate (mods.map (·.name.toString)).toList)
  let out ← IO.Process.output {
    cmd := ws.lakeEnv.lean.lean.toString
    args := #["--run", (tmp / "Image.lean").toString, (dir / name / "image.paperlean").toString,
      (tmp / "modules.txt").toString]
    env := #[("LEAN_OLEAN_PACK", some packs), ("LEAN_IMPORT_IMAGE", none),
      ("PAPERLEAN_NATIVE_LIBS", none), ("LEAN_PATH", some ws.augmentedLeanPath.toString)]
  }
  IO.FS.removeDirAll tmp
  if out.exitCode == 0 then
    -- (the last line: packages' initializers may print too)
    IO.println s!"  {((out.stdout.dropEndWhile Char.isWhitespace).toString.splitOn "\n").getLast!} entries \
      ({showTime ((← IO.monoMsNow) - start)})"
    return some s!"{name}/image.paperlean"
  else
    IO.eprintln s!"paperlean: warning: no import image, as writing it failed:\n{out.stderr}"
    return none

/-- Deletes what `data`, the new `env.json` of the data directory `dir`, does not refer to: the files of
earlier runs (and of interrupted ones), and bindings of other packs. -/
def removeUnused (dir : FilePath) (data : PreparedData) : IO Unit := do
  let used := data.packs ++ data.image?.toArray ++ data.deps.map (·.binding)
  for e in ← dir.readDir do
    let ours := isDataDirName e.fileName || ["tmp", "tmp-eval", "tmp-kept"].contains e.fileName
    if e.fileName != "bind" && ours && !used.any (·.startsWith (e.fileName ++ "/")) then
      removePath e.path
  if ← (dir / "bind").isDir then
    for e in ← (dir / "bind").readDir do
      unless used.contains s!"bind/{e.fileName}" do removePath e.path

/-- Whether the pack entry `entry` of `cdir` is there and Lean can read it (it is not, e.g., a copy). -/
def packUsable (cdir : FilePath) (entry : String) : IO Bool := do
  let pack := cdir / packFile entry
  return (← pack.pathExists) && (← Lean.PaperLean.OLeanPack.whyIgnored pack.toString).isEmpty

/-- Writes the pack entry `entry` of `cdir` of the files `files` of `pkg`, of `size` bytes, unless it is
there and usable (`packUsable`), holding its lock (another run may write it meanwhile): in a temporary
directory, which it then becomes. The entry must hold the files as `record` (`OLeanPack.hashFiles`) has
their hashes, which its key is of: a file that changed meanwhile makes it fail. -/
def writePackEntry (cdir : FilePath) (entry : String) (pkg : Package) (files : Array String) (size : Nat)
    (record : FilePath) : IO Unit :=
  Cache.withKeyLock cdir entry do
    if ← packUsable cdir entry then return
    if ← (cdir / entry).pathExists then
      removePath (cdir / entry)
      Cache.settleSlot cdir entry "" none
    let start ← IO.monoMsNow
    IO.println s!"Packing {pkg.prettyName} ({files.size} files)..."
    let tmp ← Cache.tempDir cdir entry
    let tmpEntry := s!"pack/{tmp.fileName.getD ""}"
    removePath tmp
    IO.FS.createDirAll tmp
    -- (the pack's index and roots area, besides copies of the files)
    let reserved := size + size / 8 + files.size * 1024 + 0x4000000
    let base ← Cache.reserveSlot cdir tmpEntry reserved
    try
      let keep : Std.HashSet String := files.foldl (·.insert ·) {}
      discard <| Lean.PaperLean.OLeanPack.create #[pkg.leanLibDir] (tmp / "pack.paperlean") base
        (storedRoots := #[pkgKey pkg]) (keep := fun f => return keep.contains f) (bound := true)
      let (bound, total) ← Lean.PaperLean.OLeanPack.bind (tmp / "pack.paperlean").toString
        #[pkg.leanLibDir.toString] #[] record.toString (tmp / "check.paperlean").toString
      removePath (tmp / "check.paperlean")
      if bound != total then
        throw <| IO.userError s!"{total - bound} files of {pkg.prettyName} changed while they were packed; \
          run `paperlean prepare` again"
      let packSize := (← (tmp / "pack.paperlean").metadata).byteSize.toNat
      if packSize > reserved then
        throw <| IO.userError s!"the pack of {pkg.prettyName} is larger than the address range reserved \
          for it"
      Cache.publishPack cdir tmpEntry entry packSize
      IO.println s!"  {pkg.prettyName}: {showBytes packSize} ({showTime ((← IO.monoMsNow) - start)})"
    catch e =>
      removePath tmp
      Cache.settleSlot cdir tmpEntry "" none
      throw e

/-- The writing part of `prepare`, into the cache and the data directory `dir`, as the run `stamp`:
unless `keepDeps` (then those of `old?` stay), the data of `deps`: their packs, of their files as they
are now, and the native libraries of the packages of `built`, from the cache, writing the entries that
are missing, and those of the others kept from `old?`; their import image; the root package's pack if
`opts.root`, else that of `old?`. -/
def prepareIn (ws : Workspace) (opts : PrepareOptions) (dir : FilePath) (stamp : String)
    (deps : Array Package) (built : Array String) (keepDeps : Bool) (depMods : Array Module)
    (rootMods rootUnbuilt : Nat) (native : Bool) (old? : Option PreparedData)
    (headers : IO.Ref ImportHeaders) : LoggerIO UInt32 := do
  let stored := storedRootsFor ws
  let cacheRoot ← cacheRootOf ws
  let cdir := Cache.buildDir cacheRoot
  IO.FS.createDirAll cdir
  Cache.withCacheUse cdir do
    let oldLibs := old?.map (·.libs) |>.getD #[]
    let lean := ws.lakeEnv.lean
    let jobs ← if opts.jobs > 0 then pure opts.jobs else autoJobs
    let mut toolchain? : Option String := none
    let mut prepared : Array PreparedPackage := #[]
    let mut image? : Option String := none
    let mut imagePacks : Array String := #[]
    let mut libs : Array PreparedNative := #[]
    let mut summary : Array String := #[]
    let mut failed : Array String := #[]
    let mut pluginCode : NameSet := {}
    -- the locks of the native entries that this run writes
    let mut locks : Array IO.FS.Handle := #[]
    if keepDeps then
      if let some old := old? then
        toolchain? := old.toolchain?
        prepared := old.deps
        image? := old.image?
        imagePacks := old.imagePacks
        libs := oldLibs
        summary := old.summary
    else if !deps.isEmpty then
      let toolchainTask ← IO.asTask (prio := .dedicated)
        (BuildData.toolchainPack cacheRoot lean.leanLibDir (keep := false))
      -- The files of the packages, hashed where the record does not have them, which every pack holds
      -- as they are now; and the `.c` files of the packages prepared now.
      let fresh := deps.filter (built.contains <| pkgKey ·)
      let current ← currentArtifact deps
      let files ← deps.mapM (packableFiles · current)
      let modsOf ← fresh.mapM fun pkg => return (← builtModules pkg).partition inDefaultLib
      let all := files.flatten ++ if native then modsOf.flatMap (·.1.map (·.cFile.toString)) else #[]
      let record := dir / "hashes.paperlean"
      let startHash ← IO.monoMsNow
      let found ← Lean.PaperLean.OLeanPack.hashFiles all (deps.flatMap fun p => #[p.leanLibDir, p.irDir])
        record jobs
      let hashes : FileHashes := (all.zip found).foldl (init := {}) fun m (f, r) =>
        if r.2.isEmpty then m else m.insert f r
      let packed := files.map (·.filter hashes.contains)
      let entries := deps.mapIdx fun i pkg =>
        s!"pack/{Cache.entryName (pkgKey pkg) (packKey pkg packed[i]! hashes)}"
      let missing ← (deps.zipIdx).filterM fun (_, i) =>
        return !packed[i]!.isEmpty && !(← packUsable cdir entries[i]!)
      let withPacks := (packed.filter (!·.isEmpty)).size
      IO.println s!"Hashed the files of {deps.size} packages ({showTime ((← IO.monoMsNow) - startHash)}); \
        {withPacks - missing.size} of their {withPacks} packs are in the cache"
      let sizeOf (fs : Array String) := fs.foldl (fun n f => n + identitySize (hashes.getD f default).1) 0
      unless ← enoughSpace cdir (missing.foldl (fun n (_, i) => n + sizeOf packed[i]!) 0) "packing" do
        return 1
      -- What the libraries that stay say is of the files that still have the contents of those of the
      -- pack that they were prepared with: those that a binding of that pack to the files now serves.
      let keptDir := dir / "tmp-kept"
      let keptLibs ← oldLibs.filterMapM fun l => do
        if built.contains l.pkg then return none
        let some pkg := deps.find? (pkgKey · == l.pkg) | return none
        let some p := old?.bind (·.deps.find? (·.pkg == l.pkg)) | return some l
        IO.FS.createDirAll keptDir
        let binding := keptDir / s!"{Cache.fileNamePart l.pkg}.paperlean"
        removePath binding
        -- (a pack that is gone from the cache binds nothing)
        let bindOld := Lean.PaperLean.OLeanPack.bind (cacheRoot / packFile p.pack).toString
          #[pkg.leanLibDir.toString] #[] record.toString binding.toString
        try discard bindOld catch _ => pure ()
        some <$> keptFindings pkg binding l
      removePath keptDir
      -- What the data holds of each dependency package, which the processes of the packages' constants
      -- and of the image read. (A package without built modules has no pack.)
      prepared := deps.mapIdx fun i pkg =>
        if packed[i]!.isEmpty then { pkg := pkgKey pkg, pack := "", binding := "" }
        else { pkg := pkgKey pkg, pack := Cache.entryPath entries[i]!
               binding := s!"bind/{(entries[i]!.drop "pack/".length).toString}.paperlean" }
      let prepared' := prepared
      -- The missing packs, written while the native libraries compile, then the bindings, with roots in
      -- the workspace relative to them, so that a moved workspace keeps its data.
      let pack : IO Unit := do
        for (pkg, i) in missing do
          writePackEntry cdir entries[i]! pkg packed[i]! (sizeOf packed[i]!) record
        IO.FS.createDirAll (dir / "bind")
        for pkg in deps, p in prepared', e in entries do
          if p.binding.isEmpty then continue
          let (bound, total) ← Lean.PaperLean.OLeanPack.bind (cdir / packFile e).toString
            #[pkg.leanLibDir.toString] (stored #[pkg.leanLibDir]) record.toString (dir / p.binding).toString
          if bound < total then
            IO.println s!"  {pkg.prettyName}: {total - bound} of the {total} files of its pack in the cache \
              differ from the workspace's, which are read from disk"
      let packTask ← IO.asTask pack .dedicated
      -- Native libraries, dependencies first: from the cache, or built for the packages of `built`
      -- whose libraries are missing, kept for the others (whose libraries, and those they are linked
      -- against, are as they were). A package is skipped if its library cannot be built or one that it
      -- depends on has none. The units of modules of all of them compile on `jobs` workers, each
      -- taking the next unit, and a library is linked when its units are compiled.
      let needsOf (pkg : Package) := (closure pkg).map (·.toString (escape := false))
      let imported : NameSet := depMods.foldl (·.insert ·.name) {}
      let mut nativeEntries : Std.HashMap String String := {}
      let mut toBuild : Array (Package × String) := #[]
      if native then
        for pkg in deps do
          let key := pkgKey pkg
          unless built.contains key do
            if let some l := oldLibs.find? (·.pkg == key) then
              if !l.failed && !l.entry.isEmpty then nativeEntries := nativeEntries.insert key l.entry
            continue
          let some i := deps.findIdx? (pkgKey · == key) | continue
          let some j := fresh.findIdx? (pkgKey · == key) | continue
          let depKeys := (needsOf pkg).filter (fun d => deps.any (pkgKey · == d)) |>.map fun d =>
            s!"{d}={nativeEntries.getD d "none"}"
          let (mods, others) := modsOf[j]!
          let kn ← nativeKey lean pkg (entries[i]!.drop "pack/".length).toString mods others hashes depKeys
          let e := s!"native/{Cache.entryName key kn}"
          nativeEntries := nativeEntries.insert key (Cache.entryPath e)
          unless ← (cdir / e / "native.json").pathExists do
            toBuild := toBuild.push (pkg, e)
      -- (the locks of the entries to write, in the order of their names, so that runs do not wait for
      -- each other in a cycle; another run may have written an entry meanwhile)
      for (_, e) in toBuild.qsort (·.2 < ·.2) do
        locks := locks.push (← Cache.lockKey cdir e)
      toBuild ← toBuild.filterM fun (_, e) => return !(← (cdir / e / "native.json").pathExists)
      let builtNow := toBuild.map (pkgKey ·.1)
      -- (first: what changes while it is built then shows as something else)
      let (inputs, plans) ← try
          let inputs ← toBuild.foldlM (init := ({} : Std.HashMap String String)) fun m (pkg, _) =>
            return m.insert (pkgKey pkg) (← nativeInputs pkg)
          pure (inputs, ← toBuild.mapM fun (pkg, _) => planNativeLib lean pkg jobs)
        catch e =>
          let _ ← IO.wait packTask
          for h in locks do h.unlock
          throw e
      let units := plans.mapIdx (fun i p => p.units.map fun (a, b) => (i, a, b)) |>.flatten
      -- per package, its plan, the results of its units, the number of those not done yet, and
      -- whether they need not be compiled, as the package is skipped
      let states ← plans.mapM fun p =>
        return (p, ← IO.mkRef (#[] : Array ModuleResult), ← IO.mkRef p.units.size, ← IO.mkRef false)
      let total := plans.foldl (· + ·.modules.size) 0
      for p in plans do
        unless p.modules.isEmpty do
          IO.println s!"Compiling the native library of {p.pkg.prettyName} ({jobs} jobs, {p.units.size} units)..."
      let startCompile ← IO.monoMsNow
      let tmps ← toBuild.mapM fun (_, e) => Cache.tempDir cdir e
      for t in tmps do
        removePath t
        IO.FS.createDirAll t
      let objects := cdir / "objects"
      IO.FS.createDirAll objects
      -- (of the packages whose libraries are built, whose code calls their dependencies' code; after
      -- the packs and bindings, which the process reads)
      let verdictsTask ← IO.mapTask (t := packTask) (prio := .dedicated) fun _ => do
        if plans.isEmpty then return ({} : Lean.PaperLean.EvalVerdicts)
        let tmp := dir / "tmp-eval"
        let start ← IO.monoMsNow
        let verdicts ← evalImpurities ws (toBuild.map (·.1))
          (depPacks dir cacheRoot prepared' (← IO.ofExcept (← IO.wait toolchainTask))) tmp
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
            let r ← compileNativeUnit lean objects tmps[i]! hashes plan a b
            results.modify (· ++ r)
          remaining.modify (· - 1)
          progress (b - a)
      let workers ← (List.range jobs).mapM fun _ => BaseIO.asTask worker .dedicated
      -- the units of the packages that need `key`'s library need not be compiled
      let skipDependents (key : String) : BaseIO Unit := do
        for (pkg, _) in toBuild, (_, _, _, skipped) in states do
          if (needsOf pkg).contains key then skipped.set true
      -- (on an error, after the workers and the pack and evaluation are done with the files)
      let finish : LoggerIO Unit := do
        for w in workers do
          let _ ← IO.wait w
        let _ ← IO.wait packTask
        let _ ← IO.wait verdictsTask
        for t in tmps do removePath t
        for h in locks do h.unlock
      try
        for pkg in deps do
          let key := pkgKey pkg
          for m in ← pluginModules pkg do pluginCode := pluginCode.insert m
          unless built.contains key do
            if let some lib := keptLibs.find? (·.pkg == key) then
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
          let some entry := nativeEntries[key]? | continue
          unless builtNow.contains key do
            match ← readNativeEntry cacheRoot entry with
            | some n =>
              let (l, line, left) := nativeView pkg n imported
              pluginCode := n.excluded.foldl (·.erase ·.toName) pluginCode
              libs := libs.push l
              summary := summary.push line
              IO.println s!"  {line} (from the cache)"
              examples left n
            | none =>
              summary := summary.push s!"{pkg.prettyName}: not built (its entry of the cache cannot be read)"
              failed := failed.push pkg.prettyName
              libs := libs.push { pkg := key, manifest := "", lib := "", modules := 0, failed := true }
            continue
          let some i := toBuild.findIdx? (pkgKey ·.1 == key) | continue
          let some (plan, results, remaining, _) := states[i]? | continue
          let tmp := tmps[i]!
          while (← remaining.get) > 0 do
            IO.sleep 20
          let depLibs : Array NativeLib := libs.filter (fun l => needs.contains l.pkg && l.modules > 0) |>.map fun l =>
            { pkg := l.pkg.toName, lib := cacheRoot / l.lib, manifest := cacheRoot / l.manifest, modules := l.modules,
              excluded := #[] }
          let verdicts ← IO.ofExcept (← IO.wait verdictsTask)
          let (lib?, log) ← (finishNativeLib ws plan (← results.get) depLibs tmp jobs hashes verdicts).captureLog
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
          -- (what a library does not use is interpreted, unless Lake loads its code as a plugin, which
          -- the loader then uses as Lean does; a module that it holds no code of is not its concern)
          let isPlugin (m : Name) := (pkg.findModule? m).any (·.lib.shouldPrecompile)
          pluginCode := lib.excluded.foldl (·.erase ·.1) pluginCode
          let others := plan.others.filter (!isPlugin ·.name)
          let (plugin, left) := lib.excluded.partition (isPlugin ·.1)
          let (rejected, own) := lib.interpreted.partition (isPlugin ·.1)
          let plugin := plugin ++ rejected
          let below := left ++ own
          if lib.modules == 0 && below.isEmpty && others.isEmpty && plugin.isEmpty then
            libs := libs.push { pkg := key, manifest := "", lib := "", modules := 0 }
            IO.println s!"  {pkg.prettyName}: no built modules"
            continue
          -- (dependencies come first, so that their importers are among these; which of their modules
          -- in no default library the root package imports does not change the union)
          let interpreted := libs.foldl (init := below.foldl (·.insert ·.1) ({} : NameSet)) fun s l =>
            ((l.importers ++ l.others ++ l.outdated).foldl (·.insert ·.toName)
              (l.interpreted.foldl (·.insert ·.1.toName) s))
          let scanned := (plan.modules ++ plan.others).filter (!isPlugin ·.name)
          let importers ← importersIn headers scanned (others.foldl (·.insert ·.name) interpreted)
          -- (a library's code that calls a plugin's would call its own copy: `native_libs.cpp`)
          let onPlugin := (← importersIn headers scanned pluginCode).filter fun m =>
            !importers.contains m && !interpreted.contains m
          let file (f : FilePath) := if lib.modules == 0 then "" else s!"{entry}/{f.fileName.getD ""}"
          let str (ms : Array (Name × String)) := ms.map fun (m, why) => (m.toString, why)
          let n : NativeEntry := {
            lib := {
              pkg := key, modules := lib.modules
              entry := if lib.modules == 0 then "" else entry
              manifest := file lib.manifest, lib := file lib.lib
              importers := importers.map toString
              plugin := str plugin
              others := others.map (·.name.toString)
              config := packageConfig lean pkg }
            left := str left, own := str own, onPlugin := onPlugin.map toString
            excluded := lib.excluded.map (·.1.toString) }
          if lib.modules > 0 then
            removePath (tmp / "obj")
            IO.FS.writeFile (tmp / "native.json") ((toJson n).pretty ++ "\n")
            Cache.publish cdir tmp toBuild[i]!.2
          let (l, line, left) := nativeView pkg n imported
          libs := libs.push l
          summary := summary.push line
          IO.println s!"  {line} ({showTime ((← IO.monoMsNow) - startCompile)})"
          examples left n
      catch e =>
        for (_, _, _, skipped) in states do skipped.set true
        finish
        throw e
      finish
      IO.ofExcept (← IO.wait packTask)
      toolchain? ← IO.ofExcept (← IO.wait toolchainTask)
      if toolchain?.isNone then
        IO.eprintln "paperlean: warning: no pack of Lean's library (there may not be enough disk space for \
          it); Lean reads it from disk"
      if let .ok v ← IO.wait verdictsTask then
        unless v.missing.isEmpty do
          let eg := (v.missing.toSubarray 0 3).toArray.map fun (m, why) => s!"{m} {why}"
          IO.eprintln s!"paperlean: warning: modules of the dependencies import {v.missing.size} \
            modules that cannot be imported: {", ".intercalate eg.toList}\
            {if v.missing.size > 3 then s!", and {v.missing.size - 3} more" else ""}. The modules that \
            import them run in the interpreter where no plugin loads them. Build the dependencies with \
            `lake build`, then run `paperlean prepare` again."
      -- The import image of the packs, written again if they changed.
      imagePacks := toolchain?.toArray ++ (prepared.map (·.pack)).filter (!·.isEmpty)
      if old?.any (fun old => old.imagePacks == imagePacks && old.image?.isSome) then
        image? := old?.bind (·.image?)
      else
        image? ← writeImage ws dir stamp depMods (depPacks dir cacheRoot prepared toolchain?)
    let mut packs : Array String := #[]
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
      for p in old.packs do
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
      cache := cacheRoot.toString, toolchain?, deps := prepared, packs, image?, imagePacks, summary
      native := usable.map (·.manifest)
      libs }
    data.install dir
    Cache.addUser cdir ws.dir
    Cache.touch cdir <| (prepared.map (·.pack) ++ usable.map (·.entry)).filterMap fun e =>
      (e.dropPrefix? (Cache.entryPath "")).map (·.toString)
    removeUnused dir data
    BuildData.removeEnded ws.dir
    IO.println s!"Prepared {dir}."
    unless failed.isEmpty do
      IO.eprintln s!"paperlean: warning: no native library for {", ".intercalate failed.toList} (see above), \
        so their code runs in the interpreter where no plugin loads it: the same results, but slower. \
        `paperlean status` shows this too."
    return 0

/-- A stamp for the names of the directories that a run writes in the data directory `dir`: the
monotonic clock in milliseconds, which starts again after a reboot, so made unique there. -/
def freshStamp (dir : FilePath) : IO String := do
  let mut n ← IO.monoMsNow
  while ← ["image-", "root-"].anyM fun p => (dir / s!"{p}{n}").pathExists do
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
    | some (.ok d) => d.packs ++ d.image?.toArray
    | _ => #[]
  for d in [s!"image-{stamp}", s!"root-{stamp}"] do
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
  let headers ← readImportHeaders ws
  let (imported, candidates) ← imageModules ws deps headers
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
    let packExts := #[".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir"]
    unless ← enoughSpace dir (← filesSize ws.root.leanLibDir packExts) "packing the root package" do return 1
  -- `PAPERLEAN_NO_NATIVE_PLATFORM` (any value) makes this build act as one without native
  -- libraries, for tests
  let available := Lean.PaperLean.nativeLibsAvailable &&
    (← IO.getEnv "PAPERLEAN_NO_NATIVE_PLATFORM").isNone
  if opts.native && !available && !keepDeps then
    IO.println s!"Native libraries are not available for {Platform.target} yet; preparing everything \
      else."
  let native := opts.native && available
  IO.FS.createDirAll dir
  withUnchangedData ws text? do
    let stamp ← freshStamp dir
    try
      let code ← prepareIn ws opts dir stamp deps built keepDeps depMods rootMods rootUnbuilt native old? headers
      if code == 0 then
        try writeImportHeaders dir headers catch _ => pure ()
      return code
    catch e => removeFailedRun ws dir stamp; throw e

/-- What `paperlean clean` of named packages says if it found `env.json` damaged (`why`) and reset it
(`PreparedData.empty`): none of its paths is trusted, so the files of the data stay. -/
public def damagedNote (why : String) : String :=
  s!"The prepared data was not usable: {why}. It is reset, so nothing is prepared now; its files stay \
    until `paperlean prepare` replaces them or `paperlean clean` deletes them."

/-- `paperlean clean` of the dependency packages `pkgs`: removes their prepared data and that of the
prepared packages that depend on them from the workspace's (the entries of the cache stay, for
`paperlean clean --cache`). The others keep theirs, with an import image of their packs; what was found
of their modules holds of the files that their bindings serve (`keptFindings`). -/
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
  let gone (key : String) := removed.any (pkgKey · == key)
  let deps := old.deps.filter (!gone ·.pkg)
  let headers ← readImportHeaders ws
  let (_, candidates) ← imageModules ws (allDeps.filter fun p => deps.any (·.pkg == pkgKey p)) headers
  let depMods ← candidates.filterM (·.oleanFile.pathExists)
  let others := removed.filter fun p => !pkgs.any (·.baseName == p.baseName)
  let code ← withUnchangedData ws text? do
    let stamp ← freshStamp dir
    try
      -- (without dependency packages, without the pack of Lean's library either)
      let toolchain? := if deps.isEmpty then none else old.toolchain?
      let image? ← if deps.isEmpty then pure none else
        writeImage ws dir stamp depMods (depPacks dir old.cache deps toolchain?)
      -- (what the libraries that stay say is of the files that their bindings serve)
      let libs ← (old.libs.filter (!gone ·.pkg)).mapM fun l => do
        match allDeps.find? (pkgKey · == l.pkg), deps.find? (·.pkg == l.pkg) with
        | some pkg, some p => keptFindings pkg (dir / p.binding) l
        | _, _ => pure l
      let data := { old with
        toolchain?, deps, image?, libs
        imagePacks :=
          if image?.isSome then toolchain?.toArray ++ (deps.map (·.pack)).filter (!·.isEmpty) else #[]
        native := libs.filterMap fun l => if l.modules > 0 && !l.failed then some l.manifest else none
        summary := old.summary.filter fun line => !removed.any (line.startsWith s!"{·.prettyName}: ") }
      data.install dir
      removeUnused dir data
      return 0
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
