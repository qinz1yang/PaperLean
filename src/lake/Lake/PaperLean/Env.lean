/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
import Init
public import Init.System.IO
public import Lean.Data.Json.FromToJson
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
  deriving ToJson, FromJson, Inhabited

/-- `env.json`: the prepared data and what it was prepared for; paths relative to the data directory. -/
public structure PreparedData where
  format : Nat := dataFormat
  /-- `Lean.PaperLean.version` of the writer. -/
  paperlean : String
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
  package they depend on; `none` in data written before it was recorded: all of them. -/
  packages? : Option (Array String) := none
  /-- The native libraries of `native`, by package. -/
  libs? : Option (Array PreparedNative) := none
  deriving ToJson, FromJson

/-- Why the data cannot be used by this build of PaperLean, if it cannot. -/
public def PreparedData.mismatch? (d : PreparedData) : Option String :=
  if d.format != dataFormat then some "it has a different format"
  else if d.paperlean != Lean.PaperLean.version then
    some s!"it was prepared by PaperLean {d.paperlean}, this is {Lean.PaperLean.version}"
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

/-- The prepared data of the workspace in `wsDir`: `none` if there is none, an error if `env.json`
cannot be read. -/
public def readPreparedData (wsDir : FilePath) : IO (Option (Except String PreparedData)) := do
  let file := dataDir wsDir / "env.json"
  unless ← file.pathExists do return none
  let text ← IO.FS.readFile file
  return some <| (Json.parse text >>= fromJson?).mapError (s!"{file} is damaged: {·}")

/-- The text of the workspace's `env.json`, if any: what a command that read the prepared data before
taking its lock (`withDataLock`) compares to make sure that no other command changed it meanwhile. -/
public def preparedDataText (wsDir : FilePath) : IO (Option String) := do
  let file := dataDir wsDir / "env.json"
  if ← file.pathExists then some <$> IO.FS.readFile file else pure none

/-- Writes `env.json` to `file`. -/
public def PreparedData.write (d : PreparedData) (file : FilePath) : IO Unit :=
  IO.FS.writeFile file ((toJson d).pretty ++ "\n")

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
  let vars ← do
    match ← (readPreparedData wsDir).toBaseIO with
    | .ok (some (.ok d)) => pure (if d.mismatch?.isNone then d.vars dir else #[])
    | _ => pure #[]
  for name in dataVars do
    Lean.PaperLean.setEnv name ((vars.find? (·.1 == name)).map (·.2))
  Lean.PaperLean.setEnv dataMarker (if vars.isEmpty then none else some dir.toString)

/-- The file whose lock guards the prepared data in `dir`. It lies next to `dir`, so that deleting
the data leaves it, and it is never deleted: a process that opened it while another deleted it
would otherwise lock a file that a third could no longer see. -/
public def dataLockFile (dir : FilePath) : FilePath := dir.withFileName s!"{dir.fileName.getD "paperlean"}.lock"

/--
Runs `act` holding the exclusive lock of the prepared data in `dir` (an operating-system lock on
`dataLockFile dir`, released when the process ends). If another process holds it, refuses at once
(`paperlean` commands of a workspace do not wait for each other).
-/
public def withDataLock [Monad m] [MonadFinally m] [MonadLiftT IO m] (dir : FilePath) (act : m α) : m α := do
  let lock := dataLockFile dir
  let acquire : IO IO.FS.Handle := do
    if let some parent := lock.parent then IO.FS.createDirAll parent
    -- (appending creates the file if it is missing and never truncates it)
    let h ← IO.FS.Handle.mk lock .append
    unless ← h.tryLock (exclusive := true) do
      throw <| IO.userError s!"another paperlean command is changing the prepared data in {dir}; \
        wait for it to finish. Nothing was changed."
    return h
  let h ← liftM (m := IO) acquire
  try act finally liftM (m := IO) h.unlock

end Lake.PaperLean
