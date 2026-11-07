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
import Lake.Util.Proc
import Lake.Util.NativeLib
import Lake.PaperLean.Cache
import Init.System.Platform
import Lean.Data.NameMap
public import Lean.PaperLean.NativeLibs
import Lean.PaperLean.OLeanPack
import Lean.PaperLean.System
import Lake.PaperLean.Env
import Std.Data.HashSet
public import Std.Data.HashMap

/-!
Native libraries of package modules, built with the workspace toolchain for `paperlean prepare`.
A module's native code is compiled only when its `.c`, `.ir`, `.ir.sig` and existing `.olean` parts are
bound to one Lake module trace (`Lake/Build/Common.lean`, `Lake/Build/ModuleArtifacts.lean`). Modules are
compiled in units of several, whose objects the cache keeps (`Lake.PaperLean.Cache`) by their `.c`
files and compiler arguments; a unit ends at modules picked by their names, so that a changed module
changes only the object of its unit.
-/

open System Lean

namespace Lake.PaperLean

-- (`Lean.PaperLean.ModuleNativeData` has no global instance: one in a module of `Lean` would be one
-- of every environment that imports it)
private local instance : Inhabited Lean.PaperLean.ModuleNativeData :=
  ⟨{ differs := false, metaSymbols := #[] }⟩

/-- A package's native library, built by `finishNativeLib`; without files if the package has no
built modules. -/
public structure NativeLib where
  pkg : Name            -- the package's name
  lib : FilePath        -- the shared library
  manifest : FilePath   -- its manifest (`.paperlean`)
  modules : Nat         -- the number of modules compiled into it
  /-- The package's modules left out, with the reason (no `.c`, no or stale trace, compile error, a
  symbol that nothing defines). -/
  excluded : Array (Name × String)
  /-- Its modules that run in the interpreter all the same, with the reason: every decision of the
  manifest against a module's code (`native_libs.cpp`, which decides the rest by the import). -/
  interpreted : Array (Name × String) := #[]

/-- The full identity of a checked file, as the manifest records it. -/
public structure FileStamp where
  identity : Array UInt8
  deriving BEq

/-- A file checked against a module trace. -/
public structure CheckedFile where
  path : FilePath
  stamp : FileStamp

/-- One output of a module that must be checked against its trace. -/
structure ArtifactSpec where
  kind : String
  path : FilePath
  descr? : Option ArtifactDescr

/-- A module whose files match one trace, with its object path. -/
public structure VerifiedModule where
  mod : Module
  c : FilePath
  olean : FilePath
  oleanServer? : Option FilePath
  oleanPrivate? : Option FilePath
  irSig? : Option FilePath
  ir? : Option FilePath
  files : Array CheckedFile
  obj : FilePath := ""

/-- The metadata of a regular file, or `none` if it is missing or not a regular file. -/
def statFile (file : FilePath) : BaseIO (Option FileStamp) := do
  match (← file.metadata.toBaseIO) with
  | .ok info =>
    if info.type == IO.FS.FileType.file then
      return (← Lean.PaperLean.fileIdentity file.toString).map fun id => { identity := id.data }
    else
      return none
  | .error _ => return none

/-- A positive lexical profile of the output of EmitC. Unknown inputs use ordinary Lean. -/
@[noinline] private def portableEmittedC (bytes : @& ByteArray) : Bool :=
  Lean.PaperLean.portableEmittedC bytes

@[noinline] private def portableCSymbolGuard (bytes : @& ByteArray) (symbols : @& Array String) : Option String :=
  Lean.PaperLean.portableCSymbolGuard bytes symbols

private def symbolGuardPath (snapshot : FilePath) := snapshot.addExtension "symbols.h"

/-- The content hashes of files (`Lean.PaperLean.OLeanPack.hashFiles`), by path, with the identity
that each was hashed with. -/
public abbrev FileHashes := Std.HashMap String (ByteArray × String)

/-- The content hash of `f` if it was hashed with the identity `stamp`. -/
def FileHashes.of? (hashes : FileHashes) (f : FilePath) (stamp : FileStamp) : Option String :=
  match hashes[f.toString]? with
  | some (id, h) => if id.data == stamp.identity then some h else none
  | none => none

/-- The small result of inspecting verified `.olean` parts. The parts themselves are released
before the next module is checked. Only this private staging directory is read when linking. -/
private def moduleDataPath (snapshot : FilePath) := snapshot.addExtension "native-data.json"

private def saveModuleData (snapshot : FilePath) (d : Lean.PaperLean.ModuleNativeData) : IO Unit :=
  IO.FS.writeFile (moduleDataPath snapshot) <|
    (toJson (d.differs, d.metaSymbols, d.exports, d.externs, d.why)).compress

private def checkedModuleData (snapshot : FilePath) : IO Lean.PaperLean.ModuleNativeData := do
  let path := (moduleDataPath snapshot).toString
  let some id ← Lean.PaperLean.fileIdentity path | throw <| IO.userError "missing verified module metadata"
  let bytes ← Lean.PaperLean.OLeanPack.readVerifiedBytes path id ""
  let some text := String.fromUTF8? bytes | throw <| IO.userError "invalid verified module metadata"
  let json ← IO.ofExcept <| Json.parse text
  let (differs, metaSymbols, exports, externs, why) ← IO.ofExcept <| fromJson?
    (α := Bool × Array String × Array String × Array String × String) json
  return { differs, metaSymbols, exports, externs, why }

/--
Check a file against its trace description. The file is hashed once, and its identity is compared
before and after hashing so that a file which changes during the check is rejected.
-/
def checkArtifact (hashes : FileHashes) (kind : String) (file : FilePath) (descr? : Option ArtifactDescr)
    (snapshot? : Option FilePath := none) :
    LoggerIO (Except String (CheckedFile × Bool)) := do
  let some descr := descr? | return .error s!"trace has no {kind} output"
  let before? ← statFile file
  let some before := before? | return .error s!"no {kind}"
  let some expected := hashes.of? file before | return .error s!"{kind} has no prepared content hash"
  if expected.isEmpty then return .error s!"{kind} has no prepared content hash"
  let .ok bytes ← (Lean.PaperLean.OLeanPack.readVerifiedBytes file.toString ⟨before.identity⟩ expected).toBaseIO
    | return .error s!"{kind} differs from its prepared identity or content hash"
  if Hash.ofByteArray bytes != descr.hash then return .error s!"{kind} does not match the trace"
  if let some snapshot := snapshot? then
    createParentDirs snapshot
    IO.FS.writeBinFile snapshot bytes
  let needsSymbols := kind == ".c" && !portableEmittedC bytes
  return .ok ({ path := file, stamp := before }, needsSymbols)

/-- Verify a module's files against its Lake trace. -/
def verifyModule (mod : Module) (snapshot : FilePath) (hashes : FileHashes) :
    LoggerIO (Except String (VerifiedModule × Bool)) := IO.FS.withTempDir fun partDir => do
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
  -- (`Lake/Config/Module.lean`). A file that the trace lists must match it; one it does
  -- not list must not exist (a `.c` and an `.olean` are always listed).
  let kinds : Array (String × FilePath × Option ArtifactDescr) := #[
    (".c", mod.cFile, some descrs.c), (".olean", mod.oleanFile, some descrs.olean),
    (".olean.server", mod.oleanServerFile, descrs.oleanServer?),
    (".olean.private", mod.oleanPrivateFile, descrs.oleanPrivate?),
    (".ir.sig", mod.irSigFile, descrs.irSig?), (".ir", mod.irFile, descrs.ir?)]
  let mut files : Array CheckedFile := #[]
  let mut present : Array Bool := #[]
  let mut needsSymbols := false
  let mut parts : Array FilePath := #[]
  for (kind, path, descr?) in kinds do
    if descr?.isNone then
      if hashes.contains path.toString then return .error s!"{kind} is in the prepared pack but absent from the trace"
      if ← path.pathExists then return .error s!"{kind} exists but the trace does not list it"
      present := present.push false
      continue
    let copy? := if path == mod.cFile then some snapshot
      else if kind.startsWith ".olean" then some (partDir / s!"module{kind}")
      else none
    match ← checkArtifact hashes kind path descr? copy? with
    | .ok (file, custom) =>
      files := files.push file
      present := present.push true
      if custom then needsSymbols := true
      if kind.startsWith ".olean" then
        if let some copy := copy? then parts := parts.push copy
    | .error e => return .error e
  let data ← Lean.PaperLean.moduleNativeData parts
  saveModuleData snapshot data
  if needsSymbols then
    let bytes ← IO.FS.readBinFile snapshot
    let some guard := portableCSymbolGuard bytes (data.exports ++ data.externs)
      | return .error "its C uses inputs outside the relocatable generated-C profile"
    IO.FS.writeFile (symbolGuardPath snapshot) guard
  let opt (i : Nat) (p : FilePath) := if present[i]! then some p else none
  return .ok ({
    mod := mod
    c := mod.cFile
    olean := mod.oleanFile
    oleanServer? := opt 2 mod.oleanServerFile
    oleanPrivate? := opt 3 mod.oleanPrivateFile
    irSig? := opt 4 mod.irSigFile
    ir? := opt 5 mod.irFile
    files := files
  }, needsSymbols)

/-- The C compiler arguments Lake uses for an exporting object (`Lake/Build/Common.lean`,
`Lake/Build/Module.lean`). -/
def objectArgs (lean : LeanInstall) (mod : Module) : Array String :=
  #["-I", lean.includeDir.toString] ++ lean.ccFlags ++
    mod.weakLeancArgs ++ mod.leancArgs ++ #["-DLEAN_EXPORTING"]

/-- A bounded set of location-independent compile and link flags for generated C. Additional file
inputs, preprocessing definitions and debug/profile paths require their own dependency keys. -/
private def moduleFlagsUsable (mod : Module) : Bool :=
  (mod.leancArgs ++ mod.weakLeancArgs).all fun s =>
    #["-O0", "-O1", "-O2", "-O3", "-Os", "-Oz", "-DNDEBUG", "-fPIC", "-fno-PIC"].contains s

private def linkFlagsUsable (pkg : Package) : Bool :=
  pkg.leanLibs.all fun lib =>
    (lib.weakLinkArgs ++ lib.linkArgs).all fun s => #["-lm", "-lLake", "-Wl,-z,text"].contains s

/-- Installed toolchain flags for the ordinary supported compiler distribution. Mutable response
files, forced includes, debug/profile options and unrecognized flags have no reusable input key. -/
private def installedFlagsUsable (lean : LeanInstall) : Bool :=
  go lean.ccFlags.toList
where
  go : List String → Bool
    | [] => true
    | "--sysroot" :: p :: rest => p == lean.sysroot.toString && go rest
    | "-isystem" :: p :: rest => p == (lean.sysroot / "include" / "clang").toString && go rest
    | flag :: rest =>
      #["-pthread", "-fstack-clash-protection", "-ffp-contract=off", "-fdata-sections",
        "-ffunction-sections", "-fPIC", "-fvisibility=hidden", "-Wno-unused-command-line-argument",
        "-nostdinc", "-O2", "-O3", "-DNDEBUG"].contains flag && go rest

/-- Resolve the normal driver. Explicit compiler/environment overrides or arbitrary commands on PATH
are not certified. The resolved installed driver and its identity also namespace retained results. -/
public def nativeCompiler? (lean : LeanInstall) : BaseIO (Option (FilePath × String)) := do
  -- Lake exposes its default system driver as LEAN_CC=cc in a workspace. It is still
  -- accepted only after resolving the first executable to the canonical system compiler below.
  let systemChoice (v : String) := !Platform.isWindows && (v == "cc" || v == "/usr/bin/cc")
  for key in #["LEAN_CC", "CC"] do
    if let some value ← IO.getEnv key then
      unless lean.customCc && systemChoice lean.cc.toString && systemChoice value do return none
  let overrides := #["CPATH", "C_INCLUDE_PATH", "CPLUS_INCLUDE_PATH", "OBJC_INCLUDE_PATH",
    "COMPILER_PATH", "GCC_EXEC_PREFIX", "GCC_COMPARE_DEBUG", "LIBRARY_PATH", "CCC_OVERRIDE_OPTIONS",
    "DEPENDENCIES_OUTPUT", "SUNPRO_DEPENDENCIES", "SDKROOT", "DEVELOPER_DIR", "MACOSX_DEPLOYMENT_TARGET",
    "DYLD_INSERT_LIBRARIES", "LD_PRELOAD"]
  unless installedFlagsUsable lean do return none
  if ← overrides.anyM fun v => return (← IO.getEnv v).isSome then return none
  let resolve : IO (Option FilePath) := do
    if !lean.customCc then
      if lean.cc != leanCcExe lean.sysroot then return none
      return some (← IO.FS.realPath lean.cc)
    unless systemChoice lean.cc.toString do return none
    let system ← IO.FS.realPath "/usr/bin/cc"
    if lean.cc.isAbsolute then return some system
    let some path ← IO.getEnv "PATH" | return none
    for dir in System.SearchPath.parse path do
      let f := dir / "cc"
      if ← f.pathExists then
        let first ← IO.FS.realPath f
        return if first == system then some first else none
    return none
  let .ok (some driver) ← resolve.toBaseIO | return none
  let some id ← Lean.PaperLean.fileIdentity driver.toString | return none
  return some (driver, s!"{driver}:{Lean.PaperLean.identityText id}")

/-- Run the admitted driver with the toolchain and system utilities only. In particular, an
unrelated PATH entry cannot supply the assembler or linker chosen by the driver. -/
private def nativeProc (lean : LeanInstall) (driver : FilePath) (args : Array String) : LogIO Unit := do
  let systemDirs : System.SearchPath := if Platform.isWindows then [] else ["/usr/bin", "/bin"]
  let path := if lean.customCc then systemDirs else lean.binDir :: systemDirs
  proc { cmd := driver.toString, args, inheritEnv := false, env := #[("PATH", some path.toString)] }

/-- The first checked file whose identity is no longer the recorded one. -/
def changedFile? (files : Array CheckedFile) : BaseIO (Option FilePath) := do
  for file in files do
    let now? ← statFile file.path
    if now? != some file.stamp then
      return some file.path
  return none

/-- Source paths retain their compiler-visible spelling. The private file holds exactly the bytes
that passed the module trace. The pack hash identifies that snapshot in a retained object key. -/
private structure CInput where
  original : FilePath
  snapshot : FilePath
  packHash : String
  guard? : Option FilePath
  deriving Inhabited

private def checkedC (tmp : FilePath) (i : Nat) : FilePath :=
  tmp / "obj" / "checked-c" / s!"{i}.c"

/-- A deterministic test barrier around the real driver, without replacing that driver or changing
its input. Both phases are bounded; a broken test cannot strand a prepare indefinitely. -/
private def compilerGate (inputs : Array CInput) (c : FilePath) (after : Bool) : IO Unit := do
  let some gate ← IO.getEnv "PAPERLEAN_NATIVE_COMPILER_GATE" | return
  let some file ← IO.getEnv "PAPERLEAN_NATIVE_COMPILER_GATE_INPUT" | return
  unless inputs.any (·.original.toString.endsWith file) do return
  let dir : FilePath := gate
  let signal := if after then "restored" else "release"
  if after && !(← (dir / "restore-required").pathExists) then return
  if after then
    let tmp := dir / "compiled.tmp"
    IO.FS.writeFile tmp "0"
    IO.FS.rename tmp (dir / "compiled")
  else
    let log ← IO.FS.Handle.mk (dir / "calls") .append
    log.putStrLn c.toString
    log.flush
    IO.FS.writeFile (dir / s!"blocked-{← IO.Process.getPID}") ""
  for _ in [:2400] do
    if ← (dir / signal).pathExists then return
    IO.sleep 100
  throw <| IO.userError s!"timed out waiting for {dir / signal}"

/-- Build and publish only from the checked inputs. The unit includes original C paths through the
private checked C files. The admitted C has only the toolchain header; stable logical module names
and byte hashes allow the same unit to be reused in another checkout. -/
private def compileCached (lean : LeanInstall) (objects tmp : FilePath) (mod : Module) (c : FilePath)
    (unit : Bool) (inputs : Array CInput) (files : Array CheckedFile) : BaseIO (Option FilePath × Log) := do
  let some (driver, compilerId) ← nativeCompiler? lean | return (none, {})
  let args := objectArgs lean mod
  let shape := #["portable-checked-c-v5", compilerId, toString unit] ++ args
  let cFiles := inputs.map (·.packHash)
  let shared := inputs.all (!·.packHash.isEmpty)
  let obj := if shared then objects / s!"{Cache.key (shape ++ cFiles)}.o"
    else tmp / s!"{Cache.key (shape.push c.toString)}.o"
  if (← statFile obj).isSome then return (some obj, {})
  -- `tmp` belongs to this package and process; distinct units have distinct `c` paths.
  let candidate := tmp / s!"{Cache.key ((shape ++ cFiles).push c.toString)}.o.tmp"
  let action : LoggerIO FilePath := do
    let check : LoggerIO Unit := do
      if let some path ← changedFile? files then
        error s!"changed during compilation: {path}"
    check
    try
      compilerGate inputs c false
      let source := if unit then c else inputs[0]!.snapshot
      let mut guards := #[]
      for f in inputs do
        if let some header := f.guard? then guards := guards ++ #["-include", header.toString]
      let names := inputs.map fun f => s!"-ffile-prefix-map={f.snapshot}={f.original}"
      liftM <| nativeProc lean driver (#["-c", "-o", candidate.toString, source.toString] ++ args ++ guards ++ names)
      compilerGate inputs c true
      check
      if (← statFile candidate).isNone then error "no object produced"
      if shared then
        Cache.withKeyLock (objects.parent.getD objects) s!"objects/{obj.fileName.getD ""}" do
          -- Check the entire unit before making any of its code visible to another prepare.
          check
          if (← statFile obj).isSome then return obj
          IO.FS.rename candidate obj
          return obj
      else
        IO.FS.rename candidate obj
        return obj
    finally
      discard <| (IO.FS.removeFile candidate).toBaseIO
  Lake.LoggerIO.captureLog action

/--
The built modules of the package's default libraries (of all its libraries if it has no default
targets): those whose `.olean` is below its library directory (a library's globs list only some; Lake
builds the others as their imports) and whose source exists (Lake keeps the files of modules that no
longer exist, e.g. after an update renamed them, and they can define the same declarations as current
ones), in a fixed order. Other libraries, e.g. of a package's tools, can define the same declarations
too, as they are never imported together.
-/
public def builtModules (pkg : Package) : IO (Array Module) := do
  let mut modules : Array Module := #[]
  if ← pkg.leanLibDir.isDir then
    for p in ← pkg.leanLibDir.walkDir do
      if p.extension == some "olean" then
        if let some rel := p.toString.dropPrefix? (pkg.leanLibDir.toString ++ "/") then
          let comps := (rel.toString.dropEnd ".olean".length).toString.splitOn "/"
          let name := comps.foldl (init := Name.anonymous) Name.mkStr
          if let some mod := pkg.findModule? name then
            if ← mod.leanFile.pathExists then
              modules := modules.push mod
  return modules.qsort fun a b => a.name.toString < b.name.toString

/-- Whether `mod` lies in a library that `lake build` of its package builds, which a native library
holds. -/
public def inDefaultLib (mod : Module) : Bool :=
  mod.pkg.defaultTargets.isEmpty || mod.pkg.defaultTargets.contains mod.lib.name

public def libraryModules (pkg : Package) : IO (Array Module) :=
  return (← builtModules pkg).filter inDefaultLib

/-- `f` of each element of `as`, on `jobs` tasks. -/
def parallelMap [Inhabited β] (jobs : Nat) (as : Array α) (f : α → IO β) : IO (Array β) := do
  let next ← IO.mkRef 0
  let out ← IO.mkRef (#[] : Array (Nat × β))
  let worker : IO Unit := do
    repeat
      let i ← next.modifyGet fun i => (i, i + 1)
      let some a := as[i]? | break
      let b ← f a
      out.modify (·.push (i, b))
  let tasks ← (List.range (max jobs 1)).mapM fun _ => IO.asTask worker
  for t in tasks do
    if let .error e ← IO.wait t then throw e
  return (← out.get).qsort (·.1 < ·.1) |>.map (·.2)

/-- `moduleNativeData` of the `.olean` parts of a module. -/
def moduleData (olean : FilePath) (server? private? : Option FilePath) : IO Lean.PaperLean.ModuleNativeData :=
  Lean.PaperLean.moduleNativeData (#[olean] ++ server?.toArray ++ private?.toArray)

/-- The program that runs `Lean.PaperLean.evalImpuritiesMain`. -/
def evalProgram : String := "import Lean.PaperLean.NativeLibs
def main (args : List String) : IO UInt32 := do
  let [modules, events, seconds, mebibytes, dir] := args | return 2
  Lean.PaperLean.evalImpuritiesMain modules events seconds.toNat! mebibytes.toNat! (some ⟨dir⟩)
  return 0
"

/-- What the constants of a module may take when `prepare` evaluates them, in seconds and mebibytes.
Native code evaluates them at every import, which official Lean does not. -/
def evalSeconds : Nat := 10
def evalMebibytes : Nat := 4096

/-- The verdicts of `Lean.PaperLean.evalImpuritiesMain` on the library modules of `pkgs`, in processes
of their own, with only the installed toolchain pack in `packs`. Package artifacts are bound to
the Prepare inventory `hashes`. A module whose constants take too long or too much memory, or end the process, is impure
too, and the others are done by another process. Each run owns its temporary directory;
`PAPERLEAN_EVAL_SECONDS` and `PAPERLEAN_EVAL_MEMORY` (in mebibytes) replace the limits, for tests, and
the events of the processes are appended to the file `PAPERLEAN_EVAL_EVENTS` if it is set. -/
public def evalImpurities (ws : Workspace) (pkgs : Array Package) (packs : String) (hashes : FileHashes) :
    IO Lean.PaperLean.EvalVerdicts := IO.FS.withTempDir fun dir => do
  -- Compile the trusted evaluator with just the toolchain, then give the inspector the workspace
  -- search roots as data. Its executing importer reads explicit private artifacts only.
  IO.FS.writeFile (dir / "search.json") (toJson ws.augmentedLeanPath).compress
  do
    let out ← IO.FS.Handle.mk (dir / "receipts.jsonl") .write
    for (path, (id, hash)) in hashes do
      unless path.endsWith ".c" do
        out.putStrLn (toJson (path, Lean.PaperLean.identityText id, hash)).compress
  let program := dir / "Eval.lean"
  IO.FS.writeFile program evalProgram
  let mods ← pkgs.flatMapM libraryModules
  let seconds := ((← IO.getEnv "PAPERLEAN_EVAL_SECONDS").bind String.toNat?).getD evalSeconds
  let mebibytes := ((← IO.getEnv "PAPERLEAN_EVAL_MEMORY").bind String.toNat?).getD evalMebibytes
  let mut decided : Std.HashSet FilePath := {}
  let mut verdicts : Lean.PaperLean.EvalVerdicts := {}
  repeat
    IO.FS.writeFile (dir / "modules.txt") <| String.join <| mods.toList.map fun m =>
      s!"{m.name}\t{m.oleanFile}\t{if decided.contains m.oleanFile then 1 else 0}\n"
    if ← (dir / "events.txt").pathExists then IO.FS.removeFile (dir / "events.txt")
    let parts := dir / "parts"
    IO.FS.createDir parts
    let child ← IO.Process.spawn {
      cmd := ws.lakeEnv.lean.lean.toString
      args := #["--run", program.toString, (dir / "modules.txt").toString, (dir / "events.txt").toString,
        toString seconds, toString mebibytes, dir.toString]
      env := #[("LEAN_OLEAN_PACK", some packs), ("LEAN_IMPORT_IMAGE", some ""),
        ("PAPERLEAN_NATIVE_LIBS", some ""), ("LEAN_PATH", none),
        ("LEAN_ABORT_ON_PANIC", none), ("LEAN_BACKTRACE", some "0")]
      stdin := .null
      stderr := .piped
    }
    let stderr ← child.stderr.readToEnd
    let exitCode ← child.wait
    IO.FS.removeDirAll parts
    let events : Array String ← do
      if ← (dir / "events.txt").pathExists then IO.FS.lines (dir / "events.txt") else pure #[]
    if let some copy ← IO.getEnv "PAPERLEAN_EVAL_EVENTS" then
      let h ← IO.FS.Handle.mk copy .append
      for e in events do h.putStrLn e
    let mut started? : Option FilePath := none
    let mut finished := false
    let before := decided.size
    for e in events do
      verdicts := verdicts.add e
      match e.splitOn "\t" with
      | ["start", f] => started? := some (f : FilePath)
      | "ok" :: f :: _ | "impure" :: f :: _ => decided := decided.insert (f : FilePath); started? := none
      | ["done"] => finished := true
      | _ => pure ()
    if finished then return verdicts
    -- the module that the process did not get past, or, if it did not get to one, all of them
    if let some f := started? then
      decided := decided.insert f
      let why := if exitCode == 3 then s!"takes more than {seconds} s" else
        s!"ends the process, or takes more than {mebibytes} MiB (exit code {exitCode})"
      verdicts := verdicts.add s!"impure\t{f}\tevaluating its constants {why}"
    else
      let why := (stderr.splitOn "\n").head?.getD ""
      for m in mods.filter (!decided.contains ·.oleanFile) do
        verdicts := verdicts.add s!"impure\t{m.oleanFile}\tits constants cannot be analysed: exit code {exitCode}: {why}"
      return verdicts
    if decided.size == before then return verdicts
  return verdicts

/-- The names of the variables that a `.c` file declares as `extern lean_object*`, of those that it
defines as `const lean_object*`, and of all variables that it defines with `LEAN_EXPORT`: a
declaration of the first kind and a definition of the second of the same name cannot be in one
translation unit, and two definitions of the third kind would be one variable there, while they are
two symbols, which cannot be linked together, otherwise. -/
@[noinline] private def cObjectNames (c : @& String) : IO (Array String × Array String × Array String) :=
  Lean.PaperLean.cObjectNames c

/-- The modules of a package's native library, and the units in which `prepare` compiles them:
ranges `[start, stop)` of `modules`, of consecutive modules with the same compiler arguments whose
`.c` files can be one translation unit, which end after a module whose name's hash is a multiple of
`unitCut` (so that adding or changing a module changes few units) unless they get too large. -/
public structure NativePlan where
  pkg : Package
  modules : Array Module
  /-- Its other built modules, which no native library holds. -/
  others : Array Module
  units : Array (Nat × Nat)

/-- The most modules in a unit, and the most bytes of `.c` files (one compiler process for several
files costs much less than one per file, but its memory grows with their size). -/
def unitSize : Nat := 64
def unitBytes : Nat := 4000000
def unitCut : UInt64 := 32

/-- The `NativePlan` of `pkg`, reading the `.c` files of its modules on `jobs` tasks (a module whose
`.c` file cannot be read is in a unit of its own, and its verification fails). -/
public def planNativeLib (lean : LeanInstall) (pkg : Package) (jobs : Nat) : IO NativePlan := do
  let (modules, others) := (← builtModules pkg).partition inDefaultLib
  -- `PAPERLEAN_UNIT_BYTES` replaces `unitBytes`, for tests
  let unitBytes := ((← IO.getEnv "PAPERLEAN_UNIT_BYTES").bind String.toNat?).getD unitBytes
  let names ← parallelMap jobs modules fun mod => do
    try
      let size := (← mod.cFile.metadata).byteSize.toNat
      return some (size, ← cObjectNames mod.cFile.toString)
    catch _ => return none
  let mut units := #[]
  let mut start := 0
  let mut bytes := 0
  let mut exts : Std.HashSet String := {}
  let mut consts : Std.HashSet String := {}
  let mut exported : Std.HashSet String := {}
  for i in [0:modules.size] do
    let some mod := modules[i]? | continue
    let some first := modules[start]? | continue
    let (size, e, c, x) := match names[i]? with
      | some (some (size, e, c, x)) => (size, e, c, x)
      | _ => (unitBytes, #[], #[], #[])
    if i > start && (i - start ≥ unitSize || bytes + size > unitBytes ||
        objectArgs lean mod != objectArgs lean first || e.any consts.contains || c.any exts.contains ||
        x.any exported.contains) then
      units := units.push (start, i)
      start := i
      bytes := 0
      exts := {}
      consts := {}
      exported := {}
    bytes := bytes + size
    exts := exts.insertMany e
    consts := consts.insertMany c
    exported := exported.insertMany x
    if hash mod.name % unitCut == 0 then
      units := units.push (start, i + 1)
      start := i + 1
      bytes := 0
      exts := {}
      consts := {}
      exported := {}
  if start < modules.size then units := units.push (start, modules.size)
  return { pkg, modules, others, units }

/-- The result of verifying and compiling a module of a plan: its index, the module, its files with
its object, or why it is left out, and the log. -/
public abbrev ModuleResult := Nat × Module × Except String VerifiedModule × Log

/-- Checks the result of compiling `vm` into `obj?`. -/
def checkCompiled (vm : VerifiedModule) (obj? : Option FilePath) : BaseIO (Except String VerifiedModule) := do
  let some obj := obj? | return .error "compile failed"
  if let some path ← changedFile? vm.files then return .error s!"changed during compilation: {path}"
  if (← statFile obj).isNone then return .error "no object produced"
  return .ok { vm with obj }

/-- The plan is a scheduling hint. Check it against the actual private inputs before combining
translation units: C can silently merge independent tentative definitions. -/
@[noinline] private def canGroupCheckedC (paths : @& Array String) : IO Bool :=
  Lean.PaperLean.canGroupCheckedC paths

/--
Verifies the modules of the unit `[start, stop)` of `plan` and compiles them into objects in `objects`
(where they may be already: `compileCached`, with the content hashes `hashes` of the `.c` files),
writing temporary files to `tmp`: those verified in one translation unit (whose `.c` file includes
theirs, with the static variables that the files of all modules have renamed), unless there is one or
that fails to compile; then each on its own, as Lake compiles them.
-/
public def compileNativeUnit (lean : LeanInstall) (objects tmp : FilePath) (hashes : FileHashes)
    (plan : NativePlan) (start stop : Nat) : BaseIO (Array ModuleResult) := do
  let mut results : Array ModuleResult := #[]
  let mut verified : Array (Nat × VerifiedModule × Log) := #[]
  let mut guarded : Std.HashSet Nat := {}
  -- Link flags apply to the whole library; finishNativeLib reports that failure once.
  unless linkFlagsUsable plan.pkg do return #[]
  let compiler ← nativeCompiler? lean
  for i in [start:stop] do
    let some mod := plan.modules[i]? | continue
    if compiler.isNone then
      results := results.push (i, mod, .error "its compiler or environment has unbound native inputs", {})
      continue
    unless moduleFlagsUsable mod do
      results := results.push (i, mod, .error "compile failed: its compiler flags have unbound native inputs", {})
      continue
    let (result?, log) ← Lake.LoggerIO.captureLog (verifyModule mod (checkedC tmp i) hashes)
    match result?.getD (.error "cannot read the module's files") with
    | .ok (vm, needsGuard) =>
      verified := verified.push (i, vm, log)
      if needsGuard then guarded := guarded.insert i
    | .error e => results := results.push (i, mod, .error e, log)
  if verified.isEmpty then return results
  let inputs := verified.map fun (i, vm, _) =>
    let snapshot := checkedC tmp i
    let packHash := (vm.files.find? (·.path == vm.c)).bind fun f => hashes.of? vm.c f.stamp
    { original := vm.c, snapshot, packHash := packHash.getD ""
      guard? := if guarded.contains i then some (symbolGuardPath snapshot) else none : CInput }
  if h : verified.size > 1 then
    let first := verified[0].2.1
    let unitC := tmp / s!"{plan.pkg.prettyName}-unit-{start}.c"
    -- `EmitC.lean`'s initialization flags (`_G_*initialized`) are the only static variables whose
    -- names all files have
    let flags := #["_G_initialized", "_G_runtime_initialized", "_G_meta_initialized"]
    let text := verified.foldl (init := ("", 0)) (fun (t, j) (i, _, _) =>
      (t ++ String.join (flags.toList.map fun f => s!"#define {f} {f}_{j}\n") ++
        s!"#include \"obj/checked-c/{i}.c\"\n" ++ String.join (flags.toList.map fun f => s!"#undef {f}\n"), j + 1)) |>.1
    let compatible := verified.all fun (_, vm, _) => objectArgs lean vm.mod == objectArgs lean first.mod
    let written ← if compatible && (← (canGroupCheckedC (inputs.map (·.snapshot.toString))).catchExceptions fun _ => pure false) then
      (do IO.FS.createDirAll tmp; IO.FS.writeFile unitC text; pure true).catchExceptions fun _ => pure false
    else pure false
    if written then
      let (obj?, clog) ← compileCached lean objects tmp first.mod unitC true inputs
        (verified.flatMap fun (_, vm, _) => vm.files)
      discard <| (IO.FS.removeFile unitC).toBaseIO
      if obj?.isSome then
        -- (the compiler's log once)
        let mut unitLog := clog
        for (i, vm, log) in verified do
          results := results.push (i, vm.mod, ← checkCompiled vm obj?, log ++ unitLog)
          unitLog := {}
        return results.qsort (·.1 < ·.1)
  for (i, vm, log) in verified, input in inputs do
    let (obj?, clog) ← compileCached lean objects tmp vm.mod vm.c false #[input] vm.files
    results := results.push (i, vm.mod, ← checkCompiled vm obj?, log ++ clog)
  return results.qsort (·.1 < ·.1)

/-- Bounded synchronization for the metadata directory-ABA regression. Ordinary builds do no
filesystem work here. The selected package pauses after the file-identity check and after its
module metadata has been consumed, to let the test restore the original directory. -/
private def metadataGate (pkg : Package) (after : Bool) : IO Unit := do
  let some gate ← IO.getEnv "PAPERLEAN_NATIVE_METADATA_GATE" | return
  unless (← IO.getEnv "PAPERLEAN_NATIVE_METADATA_PACKAGE") == some pkg.prettyName do return
  let dir : FilePath := gate
  IO.FS.writeFile (dir / (if after then "sampled" else "verified")) ""
  let wait := dir / (if after then "restored" else "replaced")
  for _ in [:1200] do
    if ← wait.pathExists then return
    IO.sleep 50
  throw <| IO.userError s!"timed out waiting for {wait}"

/--
Links into `outDir`, a directory that no prepared data refers to yet, the native library of the
package of `plan` of `ws` from the results of compiling its units (`compileNativeUnit`), linked
against the native libraries `deps` of the packages it depends on (already built), and writes its
manifest, which knows the modules' files by their content hashes `hashes`, reading the modules' data
on `jobs` tasks. Fails with a message if the library cannot be
linked or loaded; a module whose files cannot be verified or compiled is left out, and one that
refers to a symbol that nothing defines, such as a specialization that an official Lean's library has
and this toolchain's does not. Their importers stay in the library, which holds their code but does
not use it (`src/paperlean/native_libs.cpp`). `verdicts` tells which modules evaluate constants as the
interpreter does (`evalImpurities`), for the files that it read: a module whose files are not those,
or that it says nothing about, is taken not to. An `@[export]` of a symbol of Lean or of the libraries
that it is linked against is not supported: the library's calls of that symbol would run the export.
-/
public def finishNativeLibWithSymbols (ws : Workspace) (plan : NativePlan) (results : Array ModuleResult)
    (deps : Array NativeLib) (outDir : FilePath) (jobs : Nat) (hashes : FileHashes)
    (verdicts : Lean.PaperLean.EvalVerdicts) (depSymbols : Array String) : LoggerIO (NativeLib × String) := do
  let pkg := plan.pkg
  let lean := ws.lakeEnv.lean
  if plan.modules.isEmpty then
    return ({ pkg := pkg.baseName, lib := "", manifest := "", modules := 0, excluded := #[] }, "")
  unless linkFlagsUsable pkg do
    error s!"cannot build the native library of {pkg.prettyName}: its linker flags have unbound native inputs"
  let mut snapshots : Std.HashMap Name FilePath := {}
  let mut compiled : Array VerifiedModule := #[]
  let mut excluded : Array (Name × String) := #[]
  for (i, mod, result, log) in results.qsort (·.1 < ·.1) do
    let _ ← (log.filter (fun e => e.level != .error)).replay
    match result with
    | .ok vm =>
      compiled := compiled.push vm
      snapshots := snapshots.insert vm.mod.name (checkedC outDir i)
    | .error e => excluded := excluded.push (mod.name, e)
  -- Later compilations must not invalidate an earlier module before it is linked.
  let mut stable : Array VerifiedModule := #[]
  for vm in compiled do
    let changed? ← changedFile? vm.files
    match changed? with
    | some path => excluded := excluded.push (vm.mod.name, s!"changed before linking: {path}")
    | none =>
      if vm.files.all fun f => (hashes.of? f.path f.stamp).isSome then stable := stable.push vm
      else excluded := excluded.push (vm.mod.name, "its files changed while it was prepared")
  compiled := stable
  if compiled.isEmpty then
    return ({ pkg := pkg.baseName, lib := "", manifest := "", modules := 0, excluded }, "")
  let some (driver, _) ← nativeCompiler? lean | error "native compiler changed during preparation"
  -- Output names, with Lake's extension (`Lake/Util/NativeLib.lean`).
  let libName := s!"{pkg.prettyName}.{sharedLibExt}"
  let libFile := outDir / libName
  let manifestFile := outDir / s!"{pkg.prettyName}.paperlean"
  -- (a unit's object once, at the place of its first module)
  let objects := compiled.foldl (init := #[]) fun os vm => if os.contains vm.obj then os else os.push vm.obj
  let depLibs := deps.map (·.lib)
  metadataGate pkg false
  -- The same trace- and pack-checked metadata used to authorize the corresponding C input.
  let data ← try parallelMap jobs compiled fun vm => checkedModuleData snapshots[vm.mod.name]!
    catch e => error s!"cannot read the modules of {pkg.prettyName}: {e}"
  metadataGate pkg true
  let exports := (compiled.zip data).flatMap fun (vm, d) => d.exports.map (vm.mod.name, ·)
  let unclaimed ← Lean.PaperLean.undefinedSymbols (exports.map (·.2)) (depLibs.map (·.toString))
  if let some (m, e) := exports.find? (!unclaimed.contains ·.2) then
    error s!"PaperLean does not support `@[export {e}]` (in {m}), a symbol that Lean or another library \
      defines; build this package with `lake build`"
  -- The symbols that nothing defines get hidden stubs, for the library to load. What refers to them
  -- must not run. An `@[extern]` of the module itself makes it interpreted, and the importers of a
  -- module left out are not used either, whose symbols are those of a package (of a module built by
  -- Lake, which the importer can only refer to through imports). A module that refers to any other is
  -- left out; it stays in the objects, which may hold other modules.
  let symbols ← try parallelMap jobs compiled fun vm => Lean.PaperLean.cSymbols snapshots[vm.mod.name]!.toString
    catch e => error s!"cannot read the modules of {pkg.prettyName}: {e}"
  let defined : Std.HashSet String := symbols.foldl (fun s (ds, _) => s.insertMany ds) {}
  let wanted : Std.HashSet String := symbols.foldl (init := {}) fun s (_, us) =>
    us.foldl (fun s u => if defined.contains u then s else s.insert u) s
  let missing : Std.HashSet String := (← Lean.PaperLean.undefinedSymbols wanted.toArray
    (depLibs.map (·.toString))).foldl (·.insert ·) {}
  let ofPackage (s : String) := ["lp_", "initialize_", "runtime_initialize_", "meta_initialize_"].any fun p => s.startsWith p
  let mut linked : Array (VerifiedModule × Lean.PaperLean.ModuleNativeData) := #[]
  for vm in compiled, (_, us) in symbols, d in data do
    match us.find? fun u => missing.contains u && !ofPackage u && !d.externs.contains u with
    | some s => excluded := excluded.push (vm.mod.name, s!"it refers to {s}, which nothing defines")
    | none => linked := linked.push (vm, d)
  compiled := linked.map (·.1)
  let data := linked.map (·.2)
  let userLinkArgs : Array String := pkg.leanLibs.foldl (init := #[]) fun args lib =>
    args ++ lib.weakLinkArgs ++ lib.linkArgs
  -- Lake's link order: objects, libraries, package arguments, Lean's library and link flags
  -- (`Lake/Build/Common.lean`), then a run path for the sibling libraries and Lean.
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
  let stubC := outDir / "obj" / s!"{pkg.prettyName}-stubs.c"
  let stubO := outDir / "obj" / s!"{pkg.prettyName}-stubs.o"
  unless missing.isEmpty do
    IO.FS.createDirAll (outDir / "obj")
    IO.FS.writeFile stubC <| String.join <| missing.toList.map fun s =>
      s!"__attribute__((weak, visibility(\"hidden\"))) char {s}[8];\n"
    nativeProc lean driver #["-c", "-o", stubO.toString, stubC.toString, "-fPIC"]
  let linkArgs :=
    objects.map (·.toString)
    ++ (if missing.isEmpty then #[] else #[stubO.toString])
    ++ depLibs.map (·.toString)
    ++ userLinkArgs
    ++ #["-L", lean.leanLibDir.toString]
    ++ lean.ccLinkFlags true
    ++ runPathArgs
  -- `outDir` is a fresh directory that no prepared data refers to yet (`Lake/Build/Actions.lean`)
  try
    nativeProc lean driver (#["-shared", "-o", libFile.toString] ++ (← mkArgs libFile linkArgs))
  catch _ =>
    error s!"cannot link the native library of {pkg.prettyName}"
  if (← (libFile.addExtension "rsp").pathExists) then IO.FS.removeFile (libFile.addExtension "rsp")
  -- read-only (replaced by renaming), so that no tool changes a library in place while it is mapped
  IO.setAccessRights libFile { user := { read := true, execution := true },
                               group := { read := true, execution := true },
                               other := { read := true, execution := true } }
  -- (`lean` would warn on every run otherwise)
  let why ← Lean.PaperLean.loadError libFile.toString
  unless why.isEmpty do
    error s!"cannot load the native library of {pkg.prettyName}: {why}"
  -- The file paths are in `module_file_kind` order (`paperlean/olean_pack.h`).
  let notPure (vm : VerifiedModule) : Option String :=
    if let some (_, why) := verdicts.impure.find? (·.1 == vm.olean) then some why else
    let checked := (Lean.PaperLean.moduleFiles vm.olean).map fun f =>
      match vm.files.find? (·.path == f) with
      | some file => Lean.PaperLean.identityText ⟨file.stamp.identity⟩
      | none => Lean.PaperLean.noFile
    match verdicts.certified[vm.olean]? with
    | some ids => if ids == checked then none else some "its files changed after they were analysed"
    | none => some "there is no verdict about it"
  let hashOf (vm : VerifiedModule) (f? : Option FilePath) : String :=
    (f?.bind fun f => (vm.files.find? (·.path == f)).bind fun file => hashes.of? f file.stamp).getD ""
  let manifestModules : Array Lean.PaperLean.NativeManifestModule := compiled.mapIdx fun i vm => {
    name := vm.mod.name, cFile := snapshots[vm.mod.name]!.toString
    data := { data[i]! with differs := data[i]!.differs || (notPure vm).isSome }
    hashes := #[some vm.olean, vm.oleanServer?, vm.oleanPrivate?, vm.irSig?, vm.ir?].map (hashOf vm) }
  let manifestWhy ← Lean.PaperLean.writeNativeManifestFiles manifestFile.toString libFile.toString
    (deps.map (·.manifest.toString)) manifestModules depSymbols
  -- Certify only symbols of the modules that actually made it into this generation.
  let ownSymbols := data.flatMap (·.metaSymbols)
  let bytes := (toJson ownSymbols).compress.toUTF8
  IO.FS.writeBinFile (outDir / "meta-symbols.json") bytes
  -- The manifest records the files as they are now, the library holds them as they were verified.
  for vm in compiled do
    if let some path ← changedFile? vm.files then
      error s!"cannot use the native library of {pkg.prettyName}: {path} changed while it was \
        linked; run `paperlean prepare` again"
  return ({
    pkg := pkg.baseName
    lib := libFile
    manifest := manifestFile
    modules := compiled.size
    excluded := excluded
    interpreted := (compiled.zip (data.zip manifestWhy)).filterMap fun (vm, d, why) =>
      ((if d.differs then some d.why else notPure vm) <|> if why.isEmpty then none else some why).map
        (vm.mod.name, ·)
  }, Lean.PaperLean.OLeanPack.hashBytes bytes)

/-- Finish a library without a prepared dependency-symbol receipt. External meta calls are
classified conservatively. The prepare command supplies symbols from the linked entries. -/
public def finishNativeLib (ws : Workspace) (plan : NativePlan) (results : Array ModuleResult)
    (deps : Array NativeLib) (outDir : FilePath) (jobs : Nat) (hashes : FileHashes)
    (verdicts : Lean.PaperLean.EvalVerdicts) : LoggerIO NativeLib :=
  Prod.fst <$> finishNativeLibWithSymbols ws plan results deps outDir jobs hashes verdicts #[]

end Lake.PaperLean
