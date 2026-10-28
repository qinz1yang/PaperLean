/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
import Init
public import Lake.Config.Package
public import Lake.Config.Workspace
public import Lake.Util.Log
import Lake.Build.Actions
import Lake.Build.Common
import Lake.Build.ModuleArtifacts
import Lake.Build.Trace
import Lake.Config.LeanLib
import Lake.Config.Module
import Lake.Util.NativeLib
import Init.System.Platform
import Lean.Data.NameMap
import Lean.PaperLean.NativeLibs

/-!
Native libraries of package modules, built with the workspace toolchain for `paperlean prepare`.
A module's native code is compiled only when its `.c`, `.ir`, `.ir.sig` and existing `.olean` parts are
bound to one Lake module trace (`Lake/Build/Common.lean:162-174`,
`Lake/Build/ModuleArtifacts.lean:55-73`).
-/

open System Lean

namespace Lake.PaperLean

/-- A package's native library, built by `buildNativeLib`; without files if the package has no
built modules. -/
public structure NativeLib where
  pkg : Name            -- the package's name
  lib : FilePath        -- the shared library
  manifest : FilePath   -- its manifest (`.paperlean`)
  modules : Nat         -- the number of modules compiled into it
  /-- The package's modules left out, with the reason (no `.c`, no or stale trace, compile error). -/
  excluded : Array (Name × String)

/-- The size and modification time of a checked file. -/
structure FileStamp where
  byteSize : UInt64
  modified : IO.FS.SystemTime
  deriving BEq

/-- A file checked against a module trace. -/
structure CheckedFile where
  path : FilePath
  stamp : FileStamp

/-- One output of a module that must be checked against its trace. -/
structure ArtifactSpec where
  kind : String
  path : FilePath
  descr? : Option ArtifactDescr

/-- A module whose files match one trace, with its object path. -/
structure VerifiedModule where
  mod : Module
  c : FilePath
  olean : FilePath
  oleanServer? : Option FilePath
  oleanPrivate? : Option FilePath
  irSig? : Option FilePath
  ir? : Option FilePath
  files : Array CheckedFile
  obj : FilePath

/-- The metadata of a regular file, or `none` if it is missing or not a regular file. -/
def statFile (file : FilePath) : BaseIO (Option FileStamp) := do
  match (← file.metadata.toBaseIO) with
  | .ok info =>
    if info.type == IO.FS.FileType.file then
      return some { byteSize := info.byteSize, modified := info.modified }
    else
      return none
  | .error _ => return none

/--
Check a file against its trace description. The file is hashed once, and its size and modification
time are compared before and after hashing so that a file which changes during the check is rejected.
-/
def checkArtifact (kind : String) (file : FilePath) (descr? : Option ArtifactDescr) :
    LoggerIO (Except String CheckedFile) := do
  let some descr := descr? | return .error s!"trace has no {kind} output"
  let before? ← statFile file
  let some before := before? | return .error s!"no {kind}"
  -- The bytes' content hash, not the `.hash` file (`Lake/Build/Trace.lean:251-253`).
  let hash ← computeFileHash file
  let after? ← statFile file
  let some after := after? | return .error s!"{kind} disappeared during verification"
  if before != after then
    return .error s!"{kind} changed during verification"
  if hash != descr.hash then
    return .error s!"{kind} does not match the trace"
  return .ok { path := file, stamp := after }

/-- Verify a module's files against its Lake trace and give it an object path below `outDir`. -/
def verifyModule (outDir : FilePath) (mod : Module) : LoggerIO (Except String VerifiedModule) := do
  let c? ← statFile mod.cFile
  if c?.isNone then return .error "no .c"
  let trace ← readTraceFile mod.traceFile
  let traceData ← match trace with
    | .ok data => pure data
    | .missing => return .error "no trace"
    | .invalid => return .error "invalid trace"
  let some outputs := traceData.outputs? | return .error "trace has no outputs"
  let descrs ← match ModuleOutputDescrs.fromJson? outputs with
    | .ok descrs => pure descrs
    | .error e => return .error s!"invalid trace outputs: {e}"
  -- The artifact paths of the module, not paths found on a search path
  -- (`Lake/Config/Module.lean:101-132`). A file that the trace lists must match it; one it does
  -- not list must not exist (a `.c` and an `.olean` are always listed).
  let kinds : Array (String × FilePath × Option ArtifactDescr) := #[
    (".c", mod.cFile, some descrs.c), (".olean", mod.oleanFile, some descrs.olean),
    (".olean.server", mod.oleanServerFile, descrs.oleanServer?),
    (".olean.private", mod.oleanPrivateFile, descrs.oleanPrivate?),
    (".ir.sig", mod.irSigFile, descrs.irSig?), (".ir", mod.irFile, descrs.ir?)]
  let mut files : Array CheckedFile := #[]
  let mut present : Array Bool := #[]
  for (kind, path, descr?) in kinds do
    if descr?.isNone then
      if ← path.pathExists then return .error s!"{kind} exists but the trace does not list it"
      present := present.push false
      continue
    match ← checkArtifact kind path descr? with
    | .ok file => files := files.push file; present := present.push true
    | .error e => return .error e
  let opt (i : Nat) (p : FilePath) := if present[i]! then some p else none
  return .ok {
    mod := mod
    c := mod.cFile
    olean := mod.oleanFile
    oleanServer? := opt 2 mod.oleanServerFile
    oleanPrivate? := opt 3 mod.oleanPrivateFile
    irSig? := opt 4 mod.irSigFile
    ir? := opt 5 mod.irFile
    files := files
    obj := mod.filePath (outDir / "obj" / mod.pkg.prettyName) "o"
  }

/-- The C compiler arguments Lake uses for an exporting object (`Lake/Build/Common.lean:861-878`,
`Lake/Build/Module.lean:1236-1242`). -/
def objectArgs (lean : LeanInstall) (mod : Module) : Array String :=
  #["-I", lean.includeDir.toString] ++ lean.ccFlags ++
    mod.weakLeancArgs ++ mod.leancArgs ++ #["-DLEAN_EXPORTING"]

/-- Compile one verified module, capturing the compiler log instead of logging from the task. -/
def compileToObject (lean : LeanInstall) (vm : VerifiedModule) : BaseIO (Bool × Log) := do
  let action : LoggerIO Unit := liftM <|
    compileO vm.obj vm.c (moreArgs := objectArgs lean vm.mod) (compiler := lean.cc)
  let (ok?, log) ← Lake.LoggerIO.captureLog action
  return (ok?.isSome, log)

/-- The first checked file whose size or modification time is no longer the recorded one. -/
def changedFile? (files : Array CheckedFile) : BaseIO (Option FilePath) := do
  for file in files do
    let now? ← statFile file.path
    if now? != some file.stamp then
      return some file.path
  return none

/--
Builds into `outDir`, a directory that no prepared data refers to yet, the native library of package
`pkg` of `ws`, linked against the native
libraries `deps` of the packages it depends on (already built), running at most `jobs` compiler
processes at once and calling `progress done total` after each module. Fails with a message if the
library cannot be linked; a module whose files cannot be verified or compiled is left out.
-/
public def buildNativeLib (ws : Workspace) (pkg : Package) (deps : Array NativeLib)
    (outDir : FilePath) (jobs : Nat) (progress : Nat → Nat → BaseIO Unit) : LoggerIO NativeLib := do
  if Platform.isWindows then
    error "native libraries are not supported on Windows"
  if jobs = 0 then
    error "jobs must be at least 1"
  let lean := ws.lakeEnv.lean
  let _ ← IO.FS.createDirAll outDir
  -- The built modules of the package's default libraries (of all its libraries if it has no default
  -- targets): those whose `.olean` is below its library directory (a library's globs list only
  -- some; Lake builds the others as their imports) and whose source exists (Lake keeps the files of
  -- modules that no longer exist, e.g. after an update renamed them, and they can define the same
  -- declarations as current ones). Other libraries, e.g. of a package's tools, can define the same
  -- declarations too, as they are never imported together.
  let libs := pkg.leanLibs.filter fun lib => pkg.defaultTargets.isEmpty || pkg.defaultTargets.contains lib.name
  let mut modules : Array Module := #[]
  if ← pkg.leanLibDir.isDir then
    for p in ← pkg.leanLibDir.walkDir do
      if p.extension == some "olean" then
        if let some rel := p.toString.dropPrefix? (pkg.leanLibDir.toString ++ "/") then
          let comps := (rel.toString.dropEnd ".olean".length).toString.splitOn "/"
          let name := comps.foldl (init := Name.anonymous) Name.mkStr
          if let some mod := pkg.findModule? name then
            if libs.any (·.name == mod.lib.name) && (← mod.leanFile.pathExists) then
              modules := modules.push mod
  if modules.isEmpty then
    return { pkg := pkg.baseName, lib := "", manifest := "", modules := 0, excluded := #[] }
  let total := modules.size
  let done ← IO.mkRef 0
  let tick : BaseIO Unit := do
    let d ← done.modifyGet fun d => (d + 1, d + 1)
    progress d total
  -- Verify and compile on `jobs` workers, each taking the next module.
  let next ← IO.mkRef 0
  let results ← IO.mkRef (#[] : Array (Module × Except String VerifiedModule × Log))
  let worker : BaseIO Unit := do
    repeat
      let i ← next.modifyGet fun i => (i, i + 1)
      if h : i < modules.size then
        let mod := modules[i]
        let (result?, log) ← Lake.LoggerIO.captureLog (verifyModule outDir mod)
        let result := result?.getD (.error "cannot read the module's files")
        let (result, log) ← match result with
          | .ok vm =>
            let (ok, clog) ← compileToObject lean vm
            if !ok then pure (.error "compile failed", log ++ clog)
            else if let some path ← changedFile? vm.files then
              pure (.error s!"changed during compilation: {path}", log ++ clog)
            else if (← statFile vm.obj).isNone then pure (.error "no object produced", log ++ clog)
            else pure (.ok vm, log ++ clog)
          | .error e => pure (.error e, log)
        results.modify (·.push (mod, result, log))
        tick
      else
        break
  let tasks ← (List.range jobs).mapM fun _ => BaseIO.asTask worker
  for t in tasks do
    let _ ← IO.wait t
  let mut compiled : Array VerifiedModule := #[]
  let mut excluded : Array (Name × String) := #[]
  for (mod, result, log) in ← results.get do
    let _ ← (log.filter (fun e => e.level != .error)).replay
    match result with
    | .ok vm => compiled := compiled.push vm
    | .error e => excluded := excluded.push (mod.name, e)
  -- Later compilations must not invalidate an earlier module before it is linked.
  let mut stable : Array VerifiedModule := #[]
  for vm in compiled do
    let changed? ← changedFile? vm.files
    match changed? with
    | some path => excluded := excluded.push (vm.mod.name, s!"changed before linking: {path}")
    | none => stable := stable.push vm
  compiled := stable
  -- Output names, with Lake's extension (`Lake/Util/NativeLib.lean:16-20`).
  let libName := s!"{pkg.prettyName}.{sharedLibExt}"
  let libFile := outDir / libName
  let manifestFile := outDir / s!"{pkg.prettyName}.paperlean"
  let objects := compiled.map (·.obj)
  let depLibs := deps.map (·.lib)
  let userLinkArgs : Array String := pkg.leanLibs.foldl (init := #[]) fun args lib =>
    args ++ lib.weakLinkArgs ++ lib.linkArgs
  -- Lake's link order: objects, libraries, package arguments, Lean's library and link flags
  -- (`Lake/Build/Common.lean:950-956`), then a run path for the sibling libraries and Lean.
  -- The libraries it is linked against in other directories (e.g. those that an earlier `prepare`
  -- built and this one keeps) are found there: relative to its own directory if theirs is next to it.
  let origin := if Platform.isOSX then "@loader_path" else "$ORIGIN"
  let depDirs := deps.foldl (init := #[]) fun (ds : Array String) d =>
    match d.lib.parent with
    | some p =>
      let dirArg := if p.parent == outDir.parent then s!"{origin}/../{p.fileName.getD ""}" else p.toString
      if p == outDir || ds.contains dirArg then ds else ds.push dirArg
    | none => ds
  let depDirArgs := depDirs.map (s!"-Wl,-rpath,{·}")
  let runPathArgs :=
    if Platform.isOSX then
      #[s!"-Wl,-install_name,@rpath/{libName}", "-Wl,-rpath,@loader_path"] ++ depDirArgs ++
        #[s!"-Wl,-rpath,{lean.leanLibDir}"]
    else
      #["-Wl,-rpath,$ORIGIN"] ++ depDirArgs ++ #[s!"-Wl,-rpath,{lean.leanLibDir}",
        s!"-Wl,-soname,{libName}", "-Wl,-Bsymbolic",
        -- package code may use Lake (`import Lake`)
        "-Wl,--as-needed", "-lLake_shared", "-Wl,--no-as-needed"]
  let linkArgs :=
    objects.map (·.toString)
    ++ depLibs.map (·.toString)
    ++ userLinkArgs
    ++ #["-L", lean.leanLibDir.toString]
    ++ lean.ccLinkFlags true
    ++ runPathArgs
  -- `outDir` is a fresh directory that no prepared data refers to yet (`Lake/Build/Actions.lean:150-159`)
  try
    let _ ← compileSharedLib libFile linkArgs lean.cc
  catch _ =>
    error s!"cannot link the native library of {pkg.prettyName}"
  -- The file paths are in `module_file_kind` order (`paperlean/olean_pack.h:40-41`).
  let manifestModules : Array (Name × String × Array String) := compiled.map fun vm =>
    (vm.mod.name, vm.c.toString,
      #[vm.olean.toString,
        (vm.oleanServer?.map (·.toString)).getD "",
        (vm.oleanPrivate?.map (·.toString)).getD "",
        (vm.irSig?.map (·.toString)).getD "",
        (vm.ir?.map (·.toString)).getD ""])
  -- The public form of the native manifest writer (`Lean/PaperLean/NativeLibs.lean:18-26`).
  let _ ← Lean.PaperLean.writeNativeManifestFiles manifestFile.toString libFile.toString
    (deps.map (·.manifest.toString)) manifestModules
  return {
    pkg := pkg.baseName
    lib := libFile
    manifest := manifestFile
    modules := compiled.size
    excluded := excluded
  }

end Lake.PaperLean
