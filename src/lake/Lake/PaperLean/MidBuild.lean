/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lake.Config.Workspace
public import Lake.PaperLean.Schedule
public import Lake.PaperLean.BuildSessions
import Lake.PaperLean.Env
import Lake.PaperLean.Native
import Lake.PaperLean.Prepare
import Init.While
import Lean.Elab.ParseImportsFast
import Lean.Data.NameMap.Basic
import Std.Data.HashMap.Basic
import Lake.PaperLean.MidBuildHook

/-!
Mid-build preparation for `paperlean build` (`Lake.PaperLean.MidBuild`). In a clean build of a large
package (Mathlib, say) the package's own tactics, elaborators, linters and `initialize` code run in
the interpreter for every module compiled after them, because `paperlean prepare` ran before the
package had built modules and so prepared none of it. When the build has compiled an early fraction
of such a package (one with no current prepared data and at least `PAPERLEAN_MIDBUILD_MIN` modules,
by default 512), this session pauses the build's compile scheduler at a quiescent point, runs the
ordinary `prepare` on the modules that are built, and gives the build's later `lean` processes the
new data. The fraction is deterministic and package-independent: `max 64 (ceil (modules / 8))`; on
Mathlib's 8,564 modules that is 1,071, just past the linter layer (ranks 0-60) and the tactic layer
(`NormNum` 743, `Linarith` 954, `Ring` 1041, `Positivity` 1052 in the study's build order). No name
list is involved. A package below the minimum is never prepared, so a small project pays nothing.

This is v1: one preparation per package, at a compile barrier, serially, as the measured two-phase
cut. The barrier is the build's own scheduler (`Lake.PaperLean.Schedule`): pausing stops it from
granting slots, and the modules that already hold one finish their jobs (so their files are final)
before `prepare` reads anything. The preparation reuses `prepare` with `duringBuild` (the build
already holds the workspace's data in use, so no data lock is taken), `allowPartial` (the modules
after the cut are not built yet and are read from disk) and `keepOld` (the files of the previous
data stay for readers that still use them). Nothing here changes what a module compiles
to: the data is only a cache, its bindings and native manifests check the files' identities and
content hashes, and every failure, timeout or refusal leaves the build's environment as it was, on
the interpreter path.
`PAPERLEAN_MIDBUILD=0` turns this off, `PAPERLEAN_MIDBUILD=1` lowers the size threshold to 1 (for
tests), `PAPERLEAN_MIDBUILD_MIN` and `PAPERLEAN_MIDBUILD_DIV` set the threshold. The session is active
only under a `paperlean` command whose build uses the dependencies' prepared data (`PAPERLEAN_DATA`)
and whose scheduler is on; then the build's own pack writer (`Lake.PaperLean.BuildData`) is off, so
the data that this session publishes is what the later compiles read.
-/

open System Lean

namespace Lake.PaperLean.MidBuild

/-- A package's progress towards its first preparation. -/
private structure PkgState where
  /-- The modules of its default libraries. -/
  modules : Nat := 0
  /-- The number of finished compiled modules at which it is prepared; `0`: never. -/
  threshold : Nat := 0
  /-- The compiled modules of it that the build has finished. -/
  finished : Nat := 0
  /-- Whether a preparation has been started for it. -/
  triggered : Bool := false
  deriving Inhabited

/-- The session of one build. -/
private structure Session where
  ws : Workspace
  scheduler : Schedule.Session
  enabled : IO.Ref Bool
  packages : IO.Ref (Std.HashMap String PkgState)
  /-- The modules that the build is compiling, with the number of their compiles; keyed by package
  and name, as module names repeat across packages. -/
  running : IO.Ref (Std.HashMap String Nat)
  /-- Whether a preparation is running; one at a time (the workspace's data is shared). -/
  preparing : IO.Ref Bool
  /-- The preparations started, so that the end of the build waits for their writers. -/
  tasks : IO.Ref (List (Task (Except IO.Error Unit)))

private initialize sessions : BuildSessions Session ← BuildSessions.new

private def configNat (name : String) (dflt : Nat) : BaseIO Nat := do
  return ((← IO.getEnv name).bind (·.toNat?)).getD dflt

/-- The key of a module in `running`: its package and name. -/
private def moduleKey (mod : Module) : String :=
  mod.pkg.baseName.toString ++ "/" ++ mod.name.toString

/-- The number of modules of `pkg` that its default libraries reach: the roots that `defaultModules`
returns, closed under their source imports within the package. Lake's default library glob is the
root module alone (`lean_lib Mathlib` is `Mathlib`), so counting the glob result would count one
module for Mathlib, not the 8,564 that the root imports; the fraction has to be of the closure. -/
private partial def countClosure (pkg : Package) (todo : List Module) (seen : NameSet)
    (n : Nat) : IO Nat := do
  match todo with
  | [] => return n
  | mod :: rest =>
    let mut todo := rest
    let mut seen := seen.insert mod.name
    try
      let text ← IO.FS.readFile mod.leanFile
      let header ← Lean.parseImports' text mod.leanFile.toString
      for imp in header.imports do
        if let some m := pkg.findModule? imp.module then
          unless seen.contains m.name do
            seen := seen.insert m.name
            todo := m :: todo
    catch _ => pure ()
    countClosure pkg todo seen (n + 1)

private def moduleCount (pkg : Package) : IO Nat := do
  let roots ← defaultModules pkg
  countClosure pkg roots.toList (roots.foldl (fun s m => s.insert m.name) {}) 0

/-- Whether the package has no current prepared data for enough of its `n` modules to prepare an
early part again: no pack and no native library (a clean package); a native library of fewer than
half of its modules (an earlier partial cut); or a pack that does not serve most of the modules that
this build has built (a stale pack). A root package has no native library, so only a missing root
pack makes it eligible. Damaged data counts as none. -/
private def eligible (ws : Workspace) (pkg : Package) (n : Nat) : IO Bool := do
  let key := pkgKey pkg
  match ← readPreparedData ws.dir with
  | some (.ok d) =>
    if d.mismatch?.isSome then return true
    if pkg.baseName == ws.root.baseName then return d.packs.isEmpty
    let entry? := d.deps.find? (·.pkg == key)
    let hasPack := entry?.any (fun p => !p.pack.isEmpty)
    let native := ((d.libs.find? (·.pkg == key)).map (·.modules)).getD 0
    if !hasPack then return true
    -- A pack that serves most of the modules built so far is current; a pack that serves fewer is
    -- stale (the files changed) or is a prefix that did not cover the build.
    let fresh ← match entry? with
      | some p => do
        try
          let (stale, total) ← packStaleness pkg #[dataDir ws.dir / p.binding]
          pure (total == 0 || 2 * stale ≤ total)
        catch _ => pure false
      | none => pure false
    if !fresh then return true
    -- A current pack with a native library of less than half of the package is a partial cut: a later
    -- build extends it. A native library of at least half is left alone; the rest reads from disk.
    return native > 0 && 2 * native < n
  | _ => return true

/-- The package's state, computing its threshold once: `max 64 (ceil (modules / 8))` for a package
of at least 512 modules, and never for a smaller one (unless forced). -/
private def entryFor (session : Session) (pkg : Package) : IO PkgState := do
  let key := pkgKey pkg
  if let some st := (← session.packages.get)[key]? then return st
  let n ← moduleCount pkg
  let forced := (← IO.getEnv "PAPERLEAN_MIDBUILD") == some "1"
  let minModules ← configNat "PAPERLEAN_MIDBUILD_MIN" (if forced then 1 else 512)
  let div := max 1 (← configNat "PAPERLEAN_MIDBUILD_DIV" 8)
  let threshold :=
    if n == 0 || n < minModules then 0
    else min n (max (if n ≥ 512 then 64 else 1) ((n + div - 1) / div))
  let st : PkgState := { modules := n, threshold }
  session.packages.modify (·.insert key st)
  return st

private def compileStartingIn (session : Session) (mod : Module) : IO Unit := do
  unless ← session.enabled.get do return
  session.running.modify fun m =>
    let k := moduleKey mod
    let n := match m[k]? with | some n => n | none => 0
    m.insert k (n + 1)

/-- Counts the compile of `mod` as finished; `false` if the build did not compile it (it was read
from the cache or is not a compiled module). -/
private def compileFinished (session : Session) (mod : Module) : IO Bool := do
  session.running.modifyGet fun m =>
    let k := moduleKey mod
    match m[k]? with
    | some 1 => (true, m.erase k)
    | some n => (true, m.insert k (n - 1))
    | none => (false, m)

/-- The number of native modules of `pkg` in the workspace's current prepared data. -/
private def nativeModules (ws : Workspace) (pkg : Package) : IO Nat := do
  let key := pkgKey pkg
  match ← readPreparedData ws.dir with
  | some (.ok d) =>
    return ((d.libs.find? (·.pkg == key)).map (·.modules)).getD 0
  | _ => return 0

/-- Pauses the build's scheduler and waits until no compile job holds a slot: every file that a
compile wrote is final then. `false` if the scheduler was not idle within `timeoutMs` (the caller
resumes it). -/
private def pauseAndDrain (session : Session) (timeoutMs : Nat) : BaseIO Bool := do
  session.scheduler.pause
  let deadline := (← IO.monoMsNow) + timeoutMs
  let mut ready := false
  let mut stopped := false
  while !ready && !stopped do
    if !(← session.enabled.get) then
      stopped := true
    else if (← session.scheduler.idle) then
      ready := true
    else if (← IO.monoMsNow) ≥ deadline then
      stopped := true
    else
      IO.sleep 20
  unless ready do session.scheduler.resume
  return ready

/-- For tests: if the environment variable `var` names a directory, writes `<dir>/<tag>` there and waits
(at most four minutes) for `<dir>/<tag>.go`, so that a test can hold this point of a preparation.
`PAPERLEAN_MIDBUILD_START_GATE`: a preparation task, before it takes writer ownership (`start-<pkg>`);
`PAPERLEAN_MIDBUILD_RELOAD_GATE`: the writer, right after it took the right to replace the build's
environment (`claimed`); `PAPERLEAN_MIDBUILD_RESUME_GATE`: the coordinator, right before it resumes the
scheduler (`resume-<pkg>`). Failures of the gate itself are ignored. -/
private def testGate (var tag : String) : BaseIO Unit := do
  let some dir ← IO.getEnv var | return
  let dir : FilePath := dir
  let gate : IO Unit := do
    IO.FS.writeFile (dir / tag) ""
    for _ in [:2400] do
      if ← (dir / s!"{tag}.go").pathExists then return
      IO.sleep 100
  gate.catchExceptions fun _ => pure ()

/-- Prepares the built part of `pkg` while the build's scheduler is paused, then gives the build's
later `lean` processes the new data. Any failure leaves the environment as it was; the scheduler is
always resumed. -/
private def prepareTask (session : Session) (pkg : Package) : IO Unit := do
  if !(← session.enabled.get) then return
  let st ← entryFor session pkg
  unless ← eligible session.ws pkg st.modules do return
  testGate "PAPERLEAN_MIDBUILD_START_GATE" s!"start-{pkg.baseName}"
  let start ← session.preparing.modifyGet fun b => if b then (false, b) else (true, true)
  unless start do
    -- (another package is being prepared; let a later compile try this one again)
    session.packages.modify fun m =>
      match m[pkgKey pkg]? with
      | some st => m.insert (pkgKey pkg) { st with triggered := false }
      | none => m
    return
  -- Writer ownership (`preparing`) has up to two holders: this task, until it has finished with the
  -- scheduler (resumed it), and its writer, if one starts, until it has ended (also after a timeout,
  -- when compiles resume beside it). The last of them to finish gives it up: so no other package's
  -- preparation can pause the scheduler before this one has resumed it (`Schedule.resume` has no
  -- owner), and no second writer can run beside this one.
  let holders ← IO.mkRef (1 : Nat)
  let releaseOne : BaseIO Unit := do
    if ← holders.modifyGet (fun n => (n == 1, n - 1)) then session.preparing.set false
  try
    if !(← session.enabled.get) then return
    let st ← entryFor session pkg
    unless ← eligible session.ws pkg st.modules do return
    let timeout ← configNat "PAPERLEAN_MIDBUILD_DRAIN_MS" 900000
    unless ← pauseAndDrain session timeout do
      -- (the build did not become idle, or it ended: let a later compile try once more)
      session.packages.modify fun m =>
        match m[pkgKey pkg]? with
        | some st => m.insert (pkgKey pkg) { st with triggered := false }
        | none => m
      return
    try
      if !(← session.enabled.get) then return
      let st := ← entryFor session pkg
      unless ← eligible session.ws pkg st.modules do return
      IO.println s!"paperlean: mid-build preparation of {pkg.prettyName}: the build pauses its \
        compiles to prepare what it has built of it..."
      -- (`0` is `prepare`'s own default, `autoJobs`: the paused build runs no compile, so the
      -- preparation may use the CPUs and memory that `paperlean prepare` would)
      let jobs ← configNat "PAPERLEAN_MIDBUILD_JOBS" 0
      let opts : PrepareOptions :=
        if pkg.baseName == session.ws.root.baseName then
          { root := true, packages := some #[], duringBuild := true, allowPartial := true, keepOld := true, jobs }
        else
          { packages := some #[pkg], duringBuild := true, allowPartial := true, keepOld := true, jobs }
      -- Run the writer in a task: the build waits for it up to `PAPERLEAN_MIDBUILD_PREP_MS` and, if
      -- it takes longer, resumes on the old environment. Whether the writer gives the build the new
      -- data or the build gave up on it is ONE transition of `phase`, taken by whichever comes first
      -- (0: undecided; 1: the writer replaces the build's environment, and the build waits until it
      -- has; 2: the build gave up, and the writer leaves the environment alone): so the environment is
      -- never replaced while compiles start. The writer holds the session's writer ownership until it
      -- has really ended (`holders`), after a timeout too: no other package's writer may run beside it
      -- (both would publish the workspace's data, `duringBuild` takes no data lock). `finishFor` waits
      -- for it before the process ends.
      let phase ← IO.mkRef (0 : Nat)
      let claim (to : Nat) : BaseIO Bool := phase.modifyGet fun p => if p == 0 then (true, to) else (false, p)
      let task ← IO.asTask (prio := .dedicated) do
        try
          let (result?, log) ← Lake.LoggerIO.captureLog (prepare session.ws opts)
          if ← claim 1 then
            testGate "PAPERLEAN_MIDBUILD_RELOAD_GATE" "claimed"
            for e in log.entries do
              if e.level ≥ .warning then IO.eprintln s!"paperlean: mid-build: {e.message}"
            match result? with
            | some 0 =>
              reloadWorkspaceData session.ws.dir
              let built ← builtModules pkg
              let native ← nativeModules session.ws pkg
              let nativeNote := if native > 0 then s!" and a native library of {native} modules" else ""
              IO.println s!"paperlean: mid-build prepared {pkg.prettyName}: {built.size} modules are \
                packed{nativeNote}; later compiles of the build use it"
            | _ =>
              IO.eprintln s!"paperlean: mid-build preparation of {pkg.prettyName} did not finish; \
                the build keeps reading its modules from disk"
        catch e =>
          if ← claim 1 then
            IO.eprintln s!"paperlean: mid-build preparation of {pkg.prettyName} failed ({e}); the \
              build keeps reading its modules from disk"
      session.tasks.modify fun ts => task :: ts
      -- (the writer is a holder from here; its end gives up its share)
      holders.modify (· + 1)
      let release ← IO.mapTask (t := task) (prio := .dedicated) fun _ => releaseOne
      session.tasks.modify fun ts => release :: ts
      let prepMs ← configNat "PAPERLEAN_MIDBUILD_PREP_MS" 600000
      let deadline := (← IO.monoMsNow) + prepMs
      let mut finished := false
      let mut timedOut := false
      let mut ended := false
      while !finished && !timedOut && !ended do
        if !(← session.enabled.get) then
          ended := true
        else if ← IO.hasFinished task then
          finished := true
        else if (← IO.monoMsNow) ≥ deadline then
          timedOut := true
        else
          IO.sleep 100
      unless finished do
        if ← claim 2 then
          -- (the build ended: `finishFor` waits for the writer, and no later compile is left to use
          -- the data, so nothing is reported)
          unless ended do
            IO.eprintln s!"paperlean: mid-build preparation of {pkg.prettyName} takes longer than \
              {prepMs} ms; the build keeps the old data and waits for the writer only at its end"
          return
        -- (the writer took the build's environment first: compiles resume once it has replaced it)
      discard <| IO.wait task
    catch e =>
      IO.eprintln s!"paperlean: mid-build preparation of {pkg.prettyName} failed ({e}); the build \
        keeps reading its modules from disk"
    finally
      testGate "PAPERLEAN_MIDBUILD_RESUME_GATE" s!"resume-{pkg.baseName}"
      session.scheduler.resume
  finally
    -- (this task's share: only after the scheduler was resumed)
    releaseOne

private def moduleDoneIn (session : Session) (mod : Module) : IO Unit := do
  unless ← session.enabled.get do return
  unless ← compileFinished session mod do return
  let pkg := mod.pkg
  let st ← entryFor session pkg
  if (← IO.getEnv "PAPERLEAN_MIDBUILD_DEBUG").isSome then
    IO.eprintln s!"paperlean: midbuild done {pkg.prettyName} {st.finished + 1}/{st.modules} threshold={st.threshold}"
  if st.threshold == 0 then return
  let key := pkgKey pkg
  let fire ← session.packages.modifyGet fun m =>
    match m[key]? with
    | some cur =>
      let cur := { cur with finished := cur.finished + 1 }
      let fire := !cur.triggered && cur.finished ≥ cur.threshold
      (fire, m.insert key { cur with triggered := cur.triggered || fire })
    | none => (false, m)
  if fire then
    discard <| BaseIO.asTask (prio := .dedicated) do
      discard <| (prepareTask session pkg).toBaseIO

/-- Starts a build's mid-build preparation session, if this build uses prepared data, has the
scheduler on and did not turn it off. Without the dependencies' prepared data the build's own pack
writer (`BuildData`) is on, and this session stays off: the two writers would publish different pack
lists. -/
public def startFor (ctx : BuildContext) (ws : Workspace) (scheduler : Schedule.Session)
    (enable : Bool) : BaseIO Unit := do
  unless enable do return
  unless scheduler.active do return
  unless ← accelerated do return
  if (← IO.getEnv "PAPERLEAN_MIDBUILD") == some "0" then return
  if ← explicitDataVars then return
  unless (← IO.getEnv dataMarker).isSome do return
  sessions.insert ctx {
    ws, scheduler, enabled := ← IO.mkRef true, packages := ← IO.mkRef {}, running := ← IO.mkRef {},
    preparing := ← IO.mkRef false, tasks := ← IO.mkRef [] }

public def compileStartingFor (ctx : BuildContext) (mod : Module) : IO Unit := do
  if let some s ← sessions.find? ctx then
    try compileStartingIn s mod catch _ => pure ()

public def moduleDoneFor (ctx : BuildContext) (mod : Module) : IO Unit := do
  if let some s ← sessions.find? ctx then
    try moduleDoneIn s mod catch _ => pure ()

/-- A compile that ended with an error: it will not reach `moduleDone`, so it is no longer one of
the modules that the build compiled. -/
public def compileAbortedFor (ctx : BuildContext) (mod : Module) : IO Unit := do
  if let some s ← sessions.find? ctx then
    unless ← s.enabled.get do return
    try discard <| compileFinished s mod catch _ => pure ()

/-- Ends the session; a scheduler that a preparation paused is resumed, so that no job waits for a
preparation that the end of the build interrupted. -/
public def finishFor (ctx : BuildContext) : BaseIO Unit := do
  if let some s ← sessions.take? ctx then
    s.enabled.set false
    -- A preparation writes packs and `env.json`; the build must not end under it. A `prepareTask`
    -- takes `preparing` before it reads `enabled`, and adds its writer to `tasks` before it lets
    -- `preparing` go, so once `preparing` is free every writer started is in `tasks`. It lets go
    -- promptly: each of its waits stops when `enabled` is off. The writer's wait below is bounded by
    -- one `prepare` call.
    let mut busy ← s.preparing.get
    while busy do
      IO.sleep 20
      busy ← s.preparing.get
    let tasks ← s.tasks.get
    for t in tasks do
      discard <| IO.wait t
    s.scheduler.resume

/-- Installs this module's entry points for the upstream Lake modules, which call them through
`Lake.PaperLean.MidBuildHook` (the `paperlean` front end, before it builds). -/
public def install : BaseIO Unit :=
  MidBuildHook.install
    (MidBuildHook.Hooks.mk startFor compileStartingFor moduleDoneFor compileAbortedFor finishFor)

end Lake.PaperLean.MidBuild
