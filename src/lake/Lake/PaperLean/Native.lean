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
public import Lean.PaperLean.NativeLibs
import Lean.PaperLean.System
import Std.Data.HashSet

/-!
Native libraries of package modules, built with the workspace toolchain for `paperlean prepare`.
A module's native code is compiled only when its `.c`, `.ir`, `.ir.sig` and existing `.olean` parts are
bound to one Lake module trace (`Lake/Build/Common.lean`, `Lake/Build/ModuleArtifacts.lean`).
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
  obj : FilePath

/-- The metadata of a regular file, or `none` if it is missing or not a regular file. -/
def statFile (file : FilePath) : BaseIO (Option FileStamp) := do
  match (← file.metadata.toBaseIO) with
  | .ok info =>
    if info.type == IO.FS.FileType.file then
      return (← Lean.PaperLean.fileIdentity file.toString).map fun id => { identity := id.data }
    else
      return none
  | .error _ => return none

/--
Check a file against its trace description. The file is hashed once, and its identity is compared
before and after hashing so that a file which changes during the check is rejected.
-/
def checkArtifact (kind : String) (file : FilePath) (descr? : Option ArtifactDescr) :
    LoggerIO (Except String CheckedFile) := do
  let some descr := descr? | return .error s!"trace has no {kind} output"
  let before? ← statFile file
  let some before := before? | return .error s!"no {kind}"
  -- The bytes' content hash, not the `.hash` file (`Lake/Build/Trace.lean`).
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
  -- (`Lake/Config/Module.lean`). A file that the trace lists must match it; one it does
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

/-- The C compiler arguments Lake uses for an exporting object (`Lake/Build/Common.lean`,
`Lake/Build/Module.lean`). -/
def objectArgs (lean : LeanInstall) (mod : Module) : Array String :=
  #["-I", lean.includeDir.toString] ++ lean.ccFlags ++
    mod.weakLeancArgs ++ mod.leancArgs ++ #["-DLEAN_EXPORTING"]

/-- Compile one verified module, capturing the compiler log instead of logging from the task. -/
def compileToObject (lean : LeanInstall) (vm : VerifiedModule) : BaseIO (Bool × Log) := do
  let action : LoggerIO Unit := liftM <|
    compileO vm.obj vm.c (moreArgs := objectArgs lean vm.mod) (compiler := lean.cc)
  let (ok?, log) ← Lake.LoggerIO.captureLog action
  return (ok?.isSome, log)

/-- The first checked file whose identity is no longer the recorded one. -/
def changedFile? (files : Array CheckedFile) : BaseIO (Option FilePath) := do
  for file in files do
    let now? ← statFile file.path
    if now? != some file.stamp then
      return some file.path
  return none

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
def inDefaultLib (mod : Module) : Bool :=
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
  let [modules, events, seconds, mebibytes] := args | return 2
  Lean.PaperLean.evalImpuritiesMain modules events seconds.toNat! mebibytes.toNat!
  return 0
"

/-- What the constants of a module may take when `prepare` evaluates them, in seconds and mebibytes.
Native code evaluates them at every import, which official Lean does not. -/
def evalSeconds : Nat := 10
def evalMebibytes : Nat := 4096

/-- The verdicts of `Lean.PaperLean.evalImpuritiesMain` on the library modules of `pkgs`, in processes
of their own: with `pack` as the olean pack, as they map everything they read, and evaluate constants
of packages. A module whose constants take too long or too much memory, or end the process, is impure
too, and the others are done by another process. `dir` is a directory for their files;
`PAPERLEAN_EVAL_SECONDS` and `PAPERLEAN_EVAL_MEMORY` (in mebibytes) replace the limits, for tests. -/
public def evalImpurities (ws : Workspace) (pkgs : Array Package) (pack : FilePath) (dir : FilePath) :
    IO Lean.PaperLean.EvalVerdicts := do
  IO.FS.createDirAll dir
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
    let child ← IO.Process.spawn {
      cmd := ws.lakeEnv.lean.lean.toString
      args := #["--run", program.toString, (dir / "modules.txt").toString, (dir / "events.txt").toString,
        toString seconds, toString mebibytes]
      env := #[("LEAN_OLEAN_PACK", some pack.toString), ("LEAN_IMPORT_IMAGE", none),
        ("PAPERLEAN_NATIVE_LIBS", none), ("LEAN_PATH", some ws.augmentedLeanPath.toString),
        ("LEAN_ABORT_ON_PANIC", none), ("LEAN_BACKTRACE", some "0")]
      stdin := .null
      stderr := .piped
    }
    let stderr ← child.stderr.readToEnd
    let exitCode ← child.wait
    let events : Array String ← do
      if ← (dir / "events.txt").pathExists then IO.FS.lines (dir / "events.txt") else pure #[]
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
@[extern "lean_paperlean_c_object_names"]
opaque cObjectNames (c : @& String) : IO (Array String × Array String × Array String)

/-- The modules of a package's native library, and the units in which `prepare` compiles them:
ranges `[start, stop)` of `modules`, of consecutive modules with the same compiler arguments whose
`.c` files can be one translation unit. -/
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
  if start < modules.size then units := units.push (start, modules.size)
  return { pkg, modules, others, units }

/-- The result of verifying and compiling a module of a plan: its index, the module, its files with
its object, or why it is left out, and the log. -/
public abbrev ModuleResult := Nat × Module × Except String VerifiedModule × Log

/-- Checks the result of compiling `vm` (into `vm.obj`). -/
def checkCompiled (vm : VerifiedModule) (ok : Bool) : BaseIO (Except String VerifiedModule) := do
  if !ok then return .error "compile failed"
  if let some path ← changedFile? vm.files then return .error s!"changed during compilation: {path}"
  if (← statFile vm.obj).isNone then return .error "no object produced"
  return .ok vm

/--
Verifies the modules of the unit `[start, stop)` of `plan` and compiles them into objects below
`outDir`: those verified in one translation unit (whose `.c` file includes theirs, with the static
variables that the files of all modules have renamed), unless there is one or that fails to compile;
then each on its own, as Lake compiles them.
-/
public def compileNativeUnit (lean : LeanInstall) (outDir : FilePath) (plan : NativePlan)
    (start stop : Nat) : BaseIO (Array ModuleResult) := do
  let mut results : Array ModuleResult := #[]
  let mut verified : Array (Nat × VerifiedModule × Log) := #[]
  for i in [start:stop] do
    let some mod := plan.modules[i]? | continue
    let (result?, log) ← Lake.LoggerIO.captureLog (verifyModule outDir mod)
    match result?.getD (.error "cannot read the module's files") with
    | .ok vm => verified := verified.push (i, vm, log)
    | .error e => results := results.push (i, mod, .error e, log)
  if h : verified.size > 1 then
    let first := verified[0].2.1
    let base := outDir / "obj" / plan.pkg.prettyName / s!"unit-{start}"
    let unitC := base.addExtension "c"
    let unitO := base.addExtension "o"
    -- `EmitC.lean`'s initialization flags (`_G_*initialized`) are the only static variables whose
    -- names all files have
    let flags := #["_G_initialized", "_G_runtime_initialized", "_G_meta_initialized"]
    let text := verified.foldl (init := "") fun t (i, vm, _) =>
      t ++ String.join (flags.toList.map fun f => s!"#define {f} {f}_{i}\n") ++
        s!"#include \"{vm.c}\"\n" ++ String.join (flags.toList.map fun f => s!"#undef {f}\n")
    let written ← (do IO.FS.createDirAll (base.parent.getD outDir); IO.FS.writeFile unitC text; pure true).catchExceptions
      fun _ => pure false
    if written then
      let action : LoggerIO Unit := liftM <|
        compileO unitO unitC (moreArgs := objectArgs lean first.mod) (compiler := lean.cc)
      let (ok?, clog) ← Lake.LoggerIO.captureLog action
      if ok?.isSome && (← statFile unitO).isSome then
        -- (the compiler's log once)
        let mut unitLog := clog
        for (i, vm, log) in verified do
          results := results.push (i, vm.mod, ← checkCompiled { vm with obj := unitO } true, log ++ unitLog)
          unitLog := {}
        return results.qsort (·.1 < ·.1)
  for (i, vm, log) in verified do
    let (ok, clog) ← compileToObject lean vm
    results := results.push (i, vm.mod, ← checkCompiled vm ok, log ++ clog)
  return results.qsort (·.1 < ·.1)

/--
Links into `outDir`, a directory that no prepared data refers to yet, the native library of the
package of `plan` of `ws` from the results of compiling its units (`compileNativeUnit`), linked
against the native libraries `deps` of the packages it depends on (already built), and writes its
manifest, reading the modules' data on `jobs` tasks. Fails with a message if the library cannot be
linked or loaded; a module whose files cannot be verified or compiled is left out, and one that
refers to a symbol that nothing defines, such as a specialization that an official Lean's library has
and this toolchain's does not. Their importers stay in the library, which holds their code but does
not use it (`src/paperlean/native_libs.cpp`). `verdicts` tells which modules evaluate constants as the
interpreter does (`evalImpurities`), for the files that it read: a module whose files are not those,
or that it says nothing about, is taken not to. An `@[export]` of a symbol of Lean or of the libraries
that it is linked against is not supported: the library's calls of that symbol would run the export.
-/
public def finishNativeLib (ws : Workspace) (plan : NativePlan) (results : Array ModuleResult)
    (deps : Array NativeLib) (outDir : FilePath) (jobs : Nat)
    (verdicts : Lean.PaperLean.EvalVerdicts) : LoggerIO NativeLib := do
  let pkg := plan.pkg
  let lean := ws.lakeEnv.lean
  if plan.modules.isEmpty then
    return { pkg := pkg.baseName, lib := "", manifest := "", modules := 0, excluded := #[] }
  let mut compiled : Array VerifiedModule := #[]
  let mut excluded : Array (Name × String) := #[]
  for (_, mod, result, log) in results.qsort (·.1 < ·.1) do
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
  -- Output names, with Lake's extension (`Lake/Util/NativeLib.lean`).
  let libName := s!"{pkg.prettyName}.{sharedLibExt}"
  let libFile := outDir / libName
  let manifestFile := outDir / s!"{pkg.prettyName}.paperlean"
  -- (a unit's object once, at the place of its first module)
  let objects := compiled.foldl (init := #[]) fun os vm => if os.contains vm.obj then os else os.push vm.obj
  let depLibs := deps.map (·.lib)
  -- What the `.olean` parts of the modules and of those of the libraries it is linked against tell.
  let data ← try parallelMap jobs compiled fun vm => moduleData vm.olean vm.oleanServer? vm.oleanPrivate?
    catch e => error s!"cannot read the modules of {pkg.prettyName}: {e}"
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
  let symbols ← try parallelMap jobs compiled fun vm => Lean.PaperLean.cSymbols vm.c.toString
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
    IO.FS.writeFile stubC <| String.join <| missing.toList.map fun s =>
      s!"__attribute__((weak, visibility(\"hidden\"))) char {s}[8];\n"
    compileO stubO stubC (moreArgs := #["-fPIC"]) (compiler := lean.cc)
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
    let _ ← compileSharedLib libFile linkArgs lean.cc
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
  let mut depModules : Array Module := #[]
  for d in deps do
    if let some p := ws.packages.find? (·.baseName == d.pkg) then
      depModules := depModules ++ (← libraryModules p)
  let depData ← try parallelMap jobs depModules fun mod => do
      let opt (f : FilePath) : IO (Option FilePath) := return if ← f.pathExists then some f else none
      moduleData mod.oleanFile (← opt mod.oleanServerFile) (← opt mod.oleanPrivateFile)
    catch e => error s!"cannot read the modules that {pkg.prettyName} imports: {e}"
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
  let manifestModules : Array Lean.PaperLean.NativeManifestModule := compiled.mapIdx fun i vm => {
    name := vm.mod.name, cFile := vm.c.toString
    data := { data[i]! with differs := data[i]!.differs || (notPure vm).isSome }
    files := #[vm.olean.toString,
      (vm.oleanServer?.map (·.toString)).getD "",
      (vm.oleanPrivate?.map (·.toString)).getD "",
      (vm.irSig?.map (·.toString)).getD "",
      (vm.ir?.map (·.toString)).getD ""] }
  let manifestWhy ← Lean.PaperLean.writeNativeManifestFiles manifestFile.toString libFile.toString
    (deps.map (·.manifest.toString)) manifestModules (depData.flatMap (·.metaSymbols))
  -- The manifest records the files as they are now, the library holds them as they were verified.
  for vm in compiled do
    if let some path ← changedFile? vm.files then
      error s!"cannot use the native library of {pkg.prettyName}: {path} changed while it was \
        linked; run `paperlean prepare` again"
  return {
    pkg := pkg.baseName
    lib := libFile
    manifest := manifestFile
    modules := compiled.size
    excluded := excluded
    interpreted := (compiled.zip (data.zip manifestWhy)).filterMap fun (vm, d, why) =>
      ((if d.differs then some d.why else notPure vm) <|> if why.isEmpty then none else some why).map
        (vm.mod.name, ·)
  }

end Lake.PaperLean
