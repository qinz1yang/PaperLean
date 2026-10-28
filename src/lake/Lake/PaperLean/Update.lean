/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
import Init
public import Lake.Config.Workspace
public import Lake.Util.Log
import Lake.Util.Version
import Lake.Util.Git
import Lake.Config.Dependency
import Lake.Reservoir
import Lake.PaperLean.Env
import Lean.PaperLean.System
import Lean.Data.Json.Parser

/-!
`paperlean update`: works out what `lake update` would do to the toolchain before changing anything
(the revision each direct dependency moves to, its `lean-toolchain` read with `git show`, and Lake's
rule for the root's toolchain, `Workspace.updateToolchain`, applied to the Lean versions that
toolchains are built on), checks that there is a PaperLean release for the resulting Lean version,
and only then updates; afterwards it compares the result with the prediction and restores the old
state if they differ, which should never happen. The project keeps (or moves to) official Lean.
-/

open System Lean

namespace Lake.PaperLean

/-- The Lean version a toolchain name is built on: an official name is its own; a PaperLean release
is named `<origin>:v<PaperLean version>-lean<Lean version>`. -/
public def leanVersionOf (tc : String) : ToolchainVer :=
  let tc := (tc.dropEndWhile Char.isWhitespace).toString
  match tc.splitOn ":" with
  | [_, tag] =>
    match tag.splitOn "-lean" with
    | [_, ver] => ToolchainVer.ofString s!"leanprover/lean4:v{ver}"
    | _ => ToolchainVer.ofString tc
  | _ => ToolchainVer.ofString tc

/-- A Lean version for people: `4.35.0-rc3` rather than `leanprover/lean4:v4.35.0-rc3`. -/
def showLean (v : ToolchainVer) : String :=
  match v with
  | .release ver => toString ver
  | v => v.toString

/-- The PaperLean version of a PaperLean release name, e.g. `0.1.0` for `o/r:v0.1.0-lean4.35.0-rc3`. -/
def paperleanVersionOf? (tc : String) : Option StdVer := do
  let [_, tag] := tc.splitOn ":" | none
  let [v, _] := tag.splitOn "-lean" | none
  (StdVer.parse (if v.startsWith "v" then (v.drop 1).toString else v)).toOption

/-- `git -C dir args`: its output, if it succeeded. -/
def git (dir : FilePath) (args : Array String) : IO (Option String) := do
  let out ← IO.Process.output { cmd := "git", args := #["-C", dir.toString] ++ args }
  return if out.exitCode == 0 then some (out.stdout.dropEndWhile Char.isWhitespace).toString else none

/-- What `lake update` would do to a direct dependency of the root package. -/
structure DepPrediction where
  name : Name
  /-- Its directory, for one that moves. -/
  dir : FilePath := "."
  /-- The commit it moves to; empty for a dependency that does not move (a path). -/
  rev : String
  /-- Its `lean-toolchain` there; empty if it has none. -/
  toolchain : String
  /-- Whether its manifest fixes its toolchain. -/
  fixed : Bool

/-- The contents of a `lean-toolchain` file; empty if there is none. -/
def readToolchain (file : FilePath) : IO String := do
  if ← file.pathExists then return ((← IO.FS.readFile file).dropEndWhile Char.isWhitespace).toString
  return ""

/-- Whether a dependency's manifest fixes its toolchain, as Lake reads it
(`MaterializedDep.fixedToolchain`). -/
def fixedIn (manifest? : Option String) : Bool :=
  match manifest?.map Json.parse with
  | some (.ok j) => (j.getObjValAs? Bool "fixedToolchain").toOption.getD false
  | _ => false

/-- The `lean-toolchain` of the dependency in `dir`, and whether its manifest fixes it. -/
def readDep (dir : FilePath) : IO (String × Bool) := do
  let manifest := dir / "lake-manifest.json"
  let manifest? ← if ← manifest.pathExists then some <$> IO.FS.readFile manifest else pure none
  return (← readToolchain (dir / "lean-toolchain"), fixedIn manifest?)

/-- What `lake update` would do to a Git dependency `name` in `dir` (`url` at `rev?`); fetches the
revision without checking it out. -/
def predictGit (name : Name) (dir : FilePath) (url : String) (rev? : Option String)
    (subDir? : Option FilePath) : IO (Except String DepPrediction) := do
  -- the revision Lake fetches (`materializeGitRepo`, `Lake/Load/Materialize.lean`)
  let rev := rev?.getD Git.upstreamBranch
  let some _ ← git dir #["fetch", "--tags", "--force", "--filter=tree:0", url, rev]
    | return .error s!"cannot fetch {rev} of {url} for {name}"
  let some commit ← git dir #["rev-parse", "--verify", "--end-of-options", "FETCH_HEAD^{commit}"]
    | return .error s!"cannot resolve {rev} of {name}"
  let sub := subDir?.map (·.toString ++ "/") |>.getD ""
  let toolchain := (← git dir #["show", s!"{commit}:{sub}lean-toolchain"]).getD ""
  let fixed := fixedIn (← git dir #["show", s!"{commit}:{sub}lake-manifest.json"])
  return .ok { name, dir, rev := commit, toolchain, fixed }

/-- Predicts `lake update` of `names` (all direct dependencies if empty) of `ws` without changing
anything but the dependencies' Git objects (`git fetch`); an error says why it cannot. -/
def predict (ws : Workspace) (names : Array Name) : IO (Except String (Array DepPrediction)) := do
  let mut out := #[]
  for dep in ws.root.depConfigs do
    let dir := ws.pkgsDir / dep.dirName
    if !names.isEmpty && !names.contains dep.name then
      let (toolchain, fixed) ← readDep ((ws.findPackageByName? dep.name).map (·.dir) |>.getD dir)
      out := out.push { name := dep.name, rev := "", toolchain, fixed }
      continue
    -- the source Lake resolves (`Dependency.materialize`, `Lake/Load/Materialize.lean`)
    match dep.src? with
    | some (.path p _) =>
      let (toolchain, fixed) ← readDep (ws.dir / p)
      out := out.push { name := dep.name, rev := "", toolchain, fixed }
    | some (.git url rev? subDir?) =>
      let url := ws.lakeEnv.pkgUrlMap.find? dep.name |>.getD url
      match ← predictGit dep.name dir url rev? subDir? with
      | .ok p => out := out.push p
      | .error e => return .error e
    | none =>
      let full := s!"{dep.scope}/{dep.reservoirName}"
      let some (some pkg) ← (Reservoir.fetchPkg? ws.lakeEnv dep.scope dep.reservoirName).toBaseIO
        | return .error s!"cannot look up {full} on Reservoir"
      let some (.git _ url _ defaultBranch? subDir?) := pkg.gitSrc?
        | return .error s!"Reservoir has no Git source for {full}"
      let rev? ← match dep.version with
        | .none => pure defaultBranch?
        | .git rev => pure (some rev)
        | .ver ver =>
          let some vers ← (Reservoir.fetchPkgVersions ws.lakeEnv dep.scope dep.reservoirName).toBaseIO
            | return .error s!"cannot look up the versions of {full} on Reservoir"
          let some v := vers.find? (ver.test ·.version)
            | return .error s!"Reservoir has no version `{ver}` of {full}"
          pure (some v.revision)
      let url := ws.lakeEnv.pkgUrlMap.find? dep.name |>.getD url
      match ← predictGit dep.name (ws.pkgsDir / pkg.name) url rev? subDir? with
      | .ok p => out := out.push p
      | .error e => return .error e
  return .ok out

/-- Lake's rule for the root's toolchain after an update (`Workspace.updateToolchain`,
`Lake/Load/Resolve.lean`) over the Lean versions toolchains are built on: the newest candidate
wins, a fixed one must not be older, and incomparable candidates clash. -/
def foldToolchain (root : ToolchainVer) (rootFixed : Bool) (deps : Array DepPrediction) :
    Except String ToolchainVer := do
  let mut tc := root
  let mut fixed := rootFixed
  let mut src := "the root package"
  for dep in deps.reverse do
    if dep.toolchain.isEmpty then continue
    let v := leanVersionOf dep.toolchain
    let clash := s!"{src} needs {showLean tc}, {dep.name} needs {showLean v}"
    if dep.fixed then
      if fixed then
        unless tc == v do throw clash
      else if tc ≤ v then
        tc := v; fixed := true; src := dep.name.toString
      else throw clash
    else if v ≤ tc then pure ()
    else if !fixed && tc < v then
      tc := v; src := dep.name.toString
    else throw clash
  return tc

/-- PaperLean releases of `origin` installed in elan, and, if available, those of its GitHub
repository. -/
def releases (origin : String) : IO (Array String) := do
  let mut tcs := #[]
  let home ← match ← IO.getEnv "ELAN_HOME" with
    | some h => pure (some (FilePath.mk h))
    | none => pure ((← IO.getEnv "HOME").map (FilePath.mk · / ".elan"))
  if let some home := home then
    let dir := home / "toolchains"
    let pre := (origin.replace "/" "--") ++ "---"
    if ← dir.isDir then
      for e in ← dir.readDir do
        if let some tag := e.fileName.dropPrefix? pre then tcs := tcs.push s!"{origin}:{tag}"
  -- an origin `owner/repo` is a GitHub repository
  unless (origin.splitOn "/").length == 2 do return tcs
  let out ← (IO.Process.output { cmd := "curl", args := #["-fsSL", "--max-time", "20",
    s!"https://api.github.com/repos/{origin}/releases?per_page=100"] }).toBaseIO
  if let .ok out := out then
    if out.exitCode == 0 then
      if let .ok (.arr rs) := Json.parse out.stdout then
        for r in rs do
          if let .ok tag := r.getObjValAs? String "tag_name" then tcs := tcs.push s!"{origin}:{tag}"
  return tcs

/-- The packages of `ws` that provide a `cache` executable. -/
public def cachePackages (ws : Workspace) : Array Package :=
  ws.packages.filter fun pkg => (pkg.findLeanExe? `cache).isSome

/-- Whether `lake cache get` has something to download in `ws`: without options, it downloads the
artifacts of the packages that come from Reservoir. -/
public def fromReservoir (ws : Workspace) : Bool :=
  ws.packages.any (·.reservoirScope?.isSome)

/-- The origin of this PaperLean toolchain if it is a release, e.g. `qinz1yang/PaperLean`: from its
name in `ELAN_TOOLCHAIN` (as elan and the front end set it), or from the directory elan installed it
in, e.g. `~/.elan/toolchains/qinz1yang--PaperLean---v0.1.0-lean4.35.0-rc3`. -/
def ownOrigin? (ws : Workspace) : BaseIO (Option String) := do
  if let some tc ← IO.getEnv "ELAN_TOOLCHAIN" then
    if (paperleanVersionOf? tc).isSome then
      return some (tc.splitOn ":")[0]!
  return do
    let name ← ws.lakeEnv.lean.sysroot.fileName
    let [origin, _] := name.splitOn "---" | none
    let [owner, repo] := origin.splitOn "--" | none
    return s!"{owner}/{repo}"

/-- `paperlean update [names]` in `ws`; the exit code. The project keeps official Lean: if the update
moves it to another Lean version, its `lean-toolchain` names that official version, as with `lake
update`, and the data is prepared again with the PaperLean toolchain for it. -/
public def update (ws : Workspace) (names : Array Name) : LoggerIO UInt32 := do
  let tcFile := ws.dir / "lean-toolchain"
  let current ← readToolchain tcFile
  let release? := paperleanVersionOf? current
  -- (a toolchain given by its path is PaperLean if it has a `paperlean` command)
  let ours := release?.isSome ||
    (current.startsWith "/" && (← (FilePath.mk current / "bin" / "paperlean").pathExists))
  -- the Lean version of a PaperLean toolchain without a release name, or of a project without a
  -- toolchain, is that of this command
  let rootVer := if current.isEmpty || (ours && release?.isNone) then
      ToolchainVer.ofString s!"leanprover/lean4:v{(Lean.PaperLean.version.splitOn "-lean")[1]!}"
    else leanVersionOf current
  IO.println "Working out what an update would do..."
  let deps ← match ← predict ws names with
    | .ok deps => pure deps
    | .error e => IO.eprintln s!"paperlean: {e}. Nothing was changed."; return 1
  let target ← match foldToolchain rootVer ws.root.fixedToolchain deps with
    | .ok v => pure v
    | .error e =>
      IO.eprintln s!"paperlean: after the update, the dependencies would need different Lean versions \
        ({e}). Nothing was changed."
      return 1
  -- the toolchain after the update: official Lean, for the target version
  let changesVer := target != rootVer
  let newTc := if changesVer || ours then target.toString else current
  -- a PaperLean release for another Lean version
  let mut install? : Option String := none
  if changesVer then
    let candidates ← match ← ownOrigin? ws with
      | some origin => (·.filter (leanVersionOf · == target)) <$> releases origin
      | none => pure #[]
    let best := candidates.foldl (init := none) fun best? tc =>
      match best?, paperleanVersionOf? tc with
      | some b, some v => if (paperleanVersionOf? b).all (· < v) then some tc else best?
      | none, some _ => some tc
      | b, none => b
    let some best := best
      | IO.eprintln s!"paperlean: the update needs Lean {showLean target}, and there is no PaperLean \
          release for it. Nothing was changed.\nWith `lake update`, the project updates with official \
          Lean {showLean target}."
        return 1
    install? := some best
  let manifest := ws.manifestFile
  let savedTc ← if ← tcFile.pathExists then some <$> IO.FS.readFile tcFile else pure none
  let savedManifest ← if ← manifest.pathExists then some <$> IO.FS.readFile manifest else pure none
  let restore : IO Unit := do
    match savedTc with
    | some t => IO.FS.writeFile tcFile t
    | none => if ← tcFile.pathExists then IO.FS.removeFile tcFile
    if let some m := savedManifest then IO.FS.writeFile manifest m
    discard <| IO.Process.output { cmd := ws.lakeEnv.lake.lake.toString, args := #["resolve-deps"], cwd := ws.dir }
  let changesTc := newTc != current
  if changesTc then
    IO.println s!"The toolchain changes to {newTc}."
    IO.FS.writeFile tcFile (newTc ++ "\n")
  -- With another toolchain, elan runs its `lake` (it reads `lean-toolchain`).
  let lakeCmd := if changesTc then "lake" else ws.lakeEnv.lake.lake.toString
  let args := #["update"] ++ names.map (·.toString)
  let child ← IO.Process.spawn { cmd := lakeCmd, args, cwd := ws.dir }
  if (← child.wait) != 0 then
    IO.eprintln "paperlean: `lake update` failed; the previous state is restored."
    restore
    return 1
  -- the result must be the prediction
  let mut moved? := none
  for dep in deps do
    if dep.rev.isEmpty then continue
    let rev ← git dep.dir #["rev-parse", "HEAD"]
    if rev != some dep.rev then
      moved? := some s!"{dep.name} moved to {rev.getD "?"}, not to the predicted {dep.rev}"
  let now ← readToolchain tcFile
  if now != newTc then
    moved? := some s!"`lake update` changed the toolchain to {now}, not to the predicted {newTc}"
  if let some e := moved? then
    IO.eprintln s!"paperlean: {e}; the previous state is restored."
    restore
    return 1
  -- download built dependencies if there is a way (`paperlean cache get`), then prepare, with the
  -- PaperLean toolchain for the Lean version (the front end finds it)
  let cache := match (cachePackages ws).size with
    | 0 => fromReservoir ws
    | n => n == 1
  if let some best := install? then
    IO.println s!"Updated to Lean {showLean target}. If the PaperLean toolchain for it is not installed \
      yet, install it with `elan toolchain install {best}`; then run `paperlean \
      {if cache then "cache get" else "prepare"}`."
  IO.println s!"Updated; {if cache then "downloading and preparing" else "preparing"} the dependencies again..."
  let paperlean := if changesVer then "paperlean" else (ws.lakeEnv.lean.sysroot / "bin" / "paperlean").toString
  let child ← IO.Process.spawn { cmd := paperlean, args := if cache then #["cache", "get"] else #["prepare"], cwd := ws.dir }
  return (← child.wait)

end Lake.PaperLean
