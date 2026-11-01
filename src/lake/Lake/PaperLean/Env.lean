/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Init.System.IO
public import Lean.Data.Json.FromToJson
import Init.Data.String.Search
import Init.Data.String.TakeDrop
import Init.Meta.Defs
import Init.System.Platform
public import Lean.PaperLean.System
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer

/-!
PaperLean's prepared data of a workspace (`paperlean prepare`): olean packs, an import image and
native libraries of packages in `.lake/paperlean/`, listed by `env.json`. When a `paperlean` command
runs Lake (`accelerated`), Lake lets every `lean` it starts for the workspace use them through the
environment variables `LEAN_OLEAN_PACK`, `LEAN_IMPORT_IMAGE` and `PAPERLEAN_NATIVE_LIBS`
(`useWorkspaceData`), which enter neither Lake's traces nor its hashes. Plain `lake` commands do not.
-/

open System Lean

namespace Lake.PaperLean

/-- The directory of the prepared data of the workspace in `wsDir`. -/
public def dataDir (wsDir : FilePath) : FilePath := wsDir / ".lake" / "paperlean"

/-- The variables that prepared data sets. -/
public def dataVars : Array String := #["LEAN_OLEAN_PACK", "LEAN_IMPORT_IMAGE", "PAPERLEAN_NATIVE_LIBS"]

/-- The format of `env.json`. -/
public def dataFormat : Nat := 2

/-- A native library of prepared data; paths relative to the data directory. -/
public structure PreparedNative where
  /-- Its package (`Package.baseName`). -/
  pkg : String
  manifest : String
  lib : String
  /-- The number of modules compiled into it; none if the package has no built modules or `failed`. -/
  modules : Nat
  /-- Whether building it failed: then neither it nor the libraries of the packages that depend on
  it are used. -/
  failed : Bool := false
  /-- The modules that run in the interpreter where no plugin loads them, as they were left out of it
  or for what they hold, with the reason. Which of them a build meets only its imports can tell
  (`Lake.PaperLean.ReuseSummary.Fallbacks`). -/
  interpreted : Array (String × String) := #[]
  /-- The other modules of the package that run there likewise, as they import one that does. -/
  importers : Array String := #[]
  /-- The modules that the library does not use, with the reason, whose code Lake loads as a plugin all
  the same: they do not run in the interpreter. -/
  plugin : Array (String × String) := #[]
  /-- Its built modules in no default library that the root package's default targets do not import:
  they run in the interpreter likewise where something else imports them. -/
  others : Array String := #[]
  /-- What `packageConfig` gave when it was prepared, which all of the above holds only with. -/
  config : String := ""
  /-- If `failed`, what `nativeInputs` gave before it failed: the reason in `PreparedData.summary` is of
  that, and of `config`. -/
  inputs : String := ""
  /-- Modules that were among those above, of which that no longer holds (`keptFindings`,
  `currentFindings`): they run in the interpreter likewise, and what was found of them may no longer
  hold. -/
  outdated : Array String := #[]
  deriving ToJson, FromJson, Inhabited

/-- `env.json`: the prepared data and what it was prepared for; paths relative to the data directory. -/
public structure PreparedData where
  format : Nat := dataFormat
  /-- `Lean.PaperLean.version` of the writer. -/
  paperlean : String
  /-- `Lean.PaperLean.build` of the writer; `none` in data written before it was recorded. -/
  build? : Option String := none
  /-- `Lean.githash` of the writer. -/
  githash : String
  /-- `System.Platform.target` of the writer. -/
  platform : String
  /-- Olean packs; the import image describes the first. -/
  packs : Array String := #[]
  image? : Option String := none
  /-- Manifests of native libraries, dependencies first. -/
  native : Array String := #[]
  /-- What was prepared, for `paperlean status`. -/
  summary : Array String := #[]
  /-- The dependency packages (`Package.baseName`) whose modules the dependency pack holds, with every
  package they depend on. -/
  packages : Array String := #[]
  /-- The native libraries of `native`, by package. -/
  libs : Array PreparedNative := #[]
  deriving ToJson, FromJson

/-- Prepared data of this build that holds nothing, of no package: what `paperlean clean` of named
packages leaves of a damaged `env.json`. -/
public def PreparedData.empty : PreparedData := {
  paperlean := Lean.PaperLean.version, build? := some Lean.PaperLean.build, githash := Lean.githash
  platform := System.Platform.target }

/-- Whether `d` holds no data. -/
public def PreparedData.isEmpty (d : PreparedData) : Bool :=
  d.packs.isEmpty && d.image?.isNone && d.native.isEmpty

/-- Why the data cannot be used by this build of PaperLean, if it cannot. -/
public def PreparedData.mismatch? (d : PreparedData) : Option String :=
  if d.format != dataFormat then some "it has a different format"
  else if d.paperlean != Lean.PaperLean.version then
    some s!"it was prepared by PaperLean {d.paperlean}, this is {Lean.PaperLean.version}"
  else if d.build? != some Lean.PaperLean.build then
    some s!"it was prepared by another build of PaperLean {d.paperlean} \
      ({d.build?.getD "unknown"}), this is {Lean.PaperLean.build}"
  else if d.githash != Lean.githash then some "it was prepared by a different build of Lean"
  else if d.platform != System.Platform.target then some s!"it was prepared on {d.platform}"
  else none

/-- The values of `dataVars` for the data in `dir`. -/
public def PreparedData.vars (d : PreparedData) (dir : FilePath) : Array (String × String) :=
  let list (fs : Array String) := String.intercalate ":" (fs.map fun (f : String) => (dir / f).toString).toList
  let vars := if d.packs.isEmpty then #[] else #[("LEAN_OLEAN_PACK", list d.packs)]
  let vars := match d.image? with
    | some image => if d.packs.isEmpty then vars else vars.push ("LEAN_IMPORT_IMAGE", (dir / image).toString)
    | none => vars
  if d.native.isEmpty then vars else vars.push ("PAPERLEAN_NATIVE_LIBS", list d.native)

/-- Whether `name` is that of a directory that `paperlean prepare` writes in the data directory:
`deps-<n>`, `root-<n>` or `native-<n>` for a number `n`. -/
public def isDataDirName (name : String) : Bool :=
  ["deps-", "root-", "native-"].any fun p =>
    (name.dropPrefix? p).any fun n => !n.isEmpty && n.all Char.isDigit

/-- Whether `p`, a path of `env.json` relative to the data directory, is one that `paperlean prepare`
writes: a file in one of its directories (`isDataDirName`), so that it stays inside it. -/
public def isDataPath (p : String) : Bool :=
  match p.split '/' |>.toStringList with
  | [d, f] => isDataDirName d && !f.isEmpty && f != "." && f != ".." && !f.contains '\\'
  | _ => false

/-- `d` if every path that it holds is one that `paperlean prepare` writes (`isDataPath`); otherwise
it is damaged. -/
def PreparedData.checkPaths (d : PreparedData) : Except String PreparedData := do
  -- (a library without modules has no files)
  let libPaths := d.libs.flatMap fun l =>
    #[l.manifest, l.lib].filter (l.modules > 0 || !·.isEmpty)
  for p in d.packs ++ d.image?.toArray ++ d.native ++ libPaths do
    unless isDataPath p do throw s!"'{p}' is not a path of prepared data"
  return d

/-- The first line of `e`, without the line that names the file. -/
private def firstLine (e : IO.Error) : String :=
  ((toString e).split '\n' |>.toStringList).headD ""

/-- Whether `p` is a FIFO or another special file, which only damage puts at a side file: opening it
may never return. -/
public def isSpecialFile (p : FilePath) : BaseIO Bool := do
  match ← p.metadata.toBaseIO with
  | .ok md => return md.type == .other
  | .error _ => return false

/-- The workspace's `env.json`, if any: its text, or why it cannot be read as text. This is what a
command that read the prepared data before taking its lock (`withDataLock`) compares to make sure that
no other command changed it meanwhile. (Read in one go: another command may delete it at any time.) -/
public def preparedDataText (wsDir : FilePath) : BaseIO (Option (Except String String)) := do
  let file := dataDir wsDir / "env.json"
  if ← isSpecialFile file then return some (.error "it is not a regular file")
  match ← (IO.FS.readBinFile file).toBaseIO with
  | .ok bytes => return some ((String.fromUTF8? bytes).elim (.error "it is not UTF-8 text") .ok)
  | .error (.noFileOrDirectory ..) => return none
  | .error e => return some (.error s!"it cannot be read ({firstLine e})")

/-- The prepared data that `text?`, the `env.json` of the workspace in `wsDir` as `preparedDataText`
reads it, describes: an error if it is damaged, like one that cannot be read. -/
public def parsePreparedData (wsDir : FilePath) (text? : Option (Except String String)) :
    Option (Except String PreparedData) :=
  text?.map fun text =>
    (text >>= Json.parse >>= fromJson? >>= PreparedData.checkPaths).mapError
      (s!"{dataDir wsDir / "env.json"} is damaged: {·}")

/-- The prepared data of the workspace in `wsDir`: `none` if there is none, an error if `env.json`
is damaged or cannot be read. -/
public def readPreparedData (wsDir : FilePath) : BaseIO (Option (Except String PreparedData)) :=
  return parsePreparedData wsDir (← preparedDataText wsDir)

/-- Writes `env.json` to `file`. -/
public def PreparedData.write (d : PreparedData) (file : FilePath) : IO Unit :=
  IO.FS.writeFile file ((toJson d).pretty ++ "\n")

/-- Deletes whatever is at `p`, if anything; a symbolic link is removed itself. -/
public def removePath (p : FilePath) : IO Unit := do
  let .ok md ← p.symlinkMetadata.toBaseIO | return
  if md.type == .dir then IO.FS.removeDirAll p else IO.FS.removeFile p

/-- Writes `text` to the side file `file`, replacing what only damage puts there: a directory or a FIFO,
on which a write would fail or wait for ever, and a file that cannot be written. Whether it did. -/
public def writeSideFile (file : FilePath) (text : String) : BaseIO Bool := do
  let write : IO Unit := do
    if let .ok md ← file.metadata.toBaseIO then
      unless md.type == .file do removePath file
    IO.FS.writeFile file text
  if (← write.toBaseIO) matches .ok _ then return true
  return (← (do removePath file; IO.FS.writeFile file text : IO Unit).toBaseIO) matches .ok _

/-- Makes `d` the `env.json` of the data directory `dir`, replacing the one there whatever it is:
written to a temporary file and renamed into place, so that readers see either. -/
public def PreparedData.install (d : PreparedData) (dir : FilePath) : IO Unit := do
  let tmp := dir / "env.json.tmp"
  removePath tmp
  d.write tmp
  -- (a file cannot be renamed over a directory, which a damaged `env.json` may be)
  if ← (dir / "env.json").isDir then IO.FS.removeDirAll (dir / "env.json")
  IO.FS.rename tmp (dir / "env.json")

/-- The free disk space of `dir` in bytes; `PAPERLEAN_FREE_SPACE`, if set, replaces it, for tests. -/
public def availableSpace (dir : FilePath) : IO Nat := do
  match (← IO.getEnv "PAPERLEAN_FREE_SPACE").bind String.toNat? with
  | some n => return n
  | none => Lean.PaperLean.freeSpace dir.toString

/-- Removes the temporary files `<file>.tmp.<pid>` of writers of `file` whose process ended. -/
public def removeStaleTemps (file : FilePath) : BaseIO Unit := do
  let some dir := file.parent | return
  let some name := file.fileName | return
  let .ok entries ← dir.readDir.toBaseIO | return
  for e in entries do
    if let some pid := (e.fileName.dropPrefix? s!"{name}.tmp.").bind (·.toString.toNat?) then
      unless ← Lean.PaperLean.processAlive pid.toUInt32 do
        discard <| (IO.FS.removeFile e.path).toBaseIO

/-- Set by the `paperlean` commands for the Lake they run: only then does Lake use prepared data and
pack the modules of a build (`Lake.PaperLean.BuildData`). -/
public def acceleratedVar : String := "PAPERLEAN_ACCELERATE"

/-- Whether this Lake runs for a `paperlean` command (`acceleratedVar`). -/
public def accelerated : BaseIO Bool :=
  return (← IO.getEnv acceleratedVar) == some "1"

/-- Set with `dataVars` to the data directory whose data they are, so that processes started
later, which inherit them, can tell them from variables the user set. -/
public def dataMarker : String := "PAPERLEAN_DATA"

/-- Whether the user set any of `dataVars` (not prepared data); then prepared data is not used, so
that explicit and prepared values do not mix (an image describes its own pack). -/
public def explicitDataVars : BaseIO Bool := do
  if (← IO.getEnv dataMarker).isSome then return false
  dataVars.anyM fun v => return (← IO.getEnv v).isSome

/--
Lets every `lean` that Lake starts for the workspace in `wsDir` use its prepared data, if Lake runs
for a `paperlean` command (`accelerated`), the user set none of `dataVars` and the data is for this
build: sets them in this process, which the processes Lake starts inherit (prepared data of another
workspace that they were set to is replaced). Says nothing; `paperlean status` and `paperlean build`
report.
-/
public def useWorkspaceData (wsDir : FilePath) : BaseIO Unit := do
  unless ← accelerated do return
  if ← explicitDataVars then return
  let dir := dataDir wsDir
  if (← IO.getEnv dataMarker) == some dir.toString then return
  let vars := match ← readPreparedData wsDir with
    | some (.ok d) => if d.mismatch?.isNone then d.vars dir else #[]
    | _ => #[]
  for name in dataVars do
    Lean.PaperLean.setEnv name ((vars.find? (·.1 == name)).map (·.2))
  Lean.PaperLean.setEnv dataMarker (if vars.isEmpty then none else some dir.toString)

/-- The file whose lock guards the prepared data in `dir`, a side file
(`.lake/paperlean-lock.paperlean`). It lies next to `dir`, so that deleting the data leaves it, and it
is never deleted: a process that opened it while another deleted it would otherwise lock a file that
a third could no longer see. -/
public def dataLockFile (dir : FilePath) : FilePath :=
  dir.withFileName s!"{dir.fileName.getD "paperlean"}-lock.paperlean"

/-- Opens the file `lock`, which `withDataLock` and `withDataInUse` lock. -/
private def openDataLock (lock : FilePath) : IO IO.FS.Handle := do
  if ← isSpecialFile lock then throw <| IO.userError "it is not a regular file"
  if let some parent := lock.parent then IO.FS.createDirAll parent
  -- (appending creates the file if it is missing and never truncates it)
  IO.FS.Handle.mk lock .append

/--
Runs `act` holding the exclusive lock of the prepared data in `dir` (an operating-system lock on
`dataLockFile dir`, released when the process ends). If another process holds it, exclusively or as
a build does (`withDataInUse`), refuses at once (`paperlean` commands of a workspace do not wait for
each other). So does a lock file that cannot be opened: these commands change the data, which the lock
must protect from a build.
-/
public def withDataLock [Monad m] [MonadFinally m] [MonadLiftT IO m] (dir : FilePath) (act : m α) : m α := do
  let lock := dataLockFile dir
  let acquire : IO IO.FS.Handle := do
    let h ← try openDataLock lock catch e =>
      throw <| IO.userError s!"cannot open {lock}: {firstLine e}. If it is damaged, delete it. Nothing \
        was changed."
    unless ← h.tryLock (exclusive := true) do
      if ← h.tryLock (exclusive := false) then
        h.unlock
        throw <| IO.userError s!"a paperlean build is using the prepared data in {dir}; run this \
          command after it. Nothing was changed."
      throw <| IO.userError s!"another paperlean command is changing the prepared data in {dir}; \
        wait for it to finish. Nothing was changed."
    return h
  let h ← liftM (m := IO) acquire
  try act finally liftM (m := IO) h.unlock

/-- Runs `act`, a Lake that uses the prepared data in `dir` (a build or a download), holding a shared
lock of it, so that no command changes or deletes the data meanwhile (`withDataLock`). Refuses at
once if a command is changing it, saying that `undone` (e.g. "built") was not. If the lock file cannot
be opened, as in a project that is read-only, `act` gets why, and must not use the data. -/
public def withDataInUse [Monad m] [MonadFinally m] [MonadLiftT IO m] (dir : FilePath)
    (act : Option String → m α) (undone := "built") : m α := do
  let lock := dataLockFile dir
  let acquire : IO (Except String IO.FS.Handle) := do
    let h ← try openDataLock lock catch e =>
      return .error s!"{lock} cannot be opened: {firstLine e}"
    unless ← h.tryLock (exclusive := false) do
      throw <| IO.userError s!"another paperlean command is changing the prepared data in {dir}; \
        wait for it to finish. Nothing was {undone}."
    return .ok h
  match ← liftM (m := IO) acquire with
  | .ok h => try act none finally liftM (m := IO) h.unlock
  | .error why => act (some why)

end Lake.PaperLean
