/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Gabriel Ebner, Sebastian Ullrich
-/
module

prelude
public import Lake.Config.Workspace
import Lake.Config.Monad
import Lake.Build.Job.Monad
import Lake.Build.Index
import Init.Omega
import Lake.PaperLean.BuildData
import Lake.PaperLean.Schedule
import Lake.PaperLean.HashCache
import Lake.PaperLean.SetupIndex
import Lake.PaperLean.SourceInputScope

/-! # Build Runner

This module defines the top-level functions used to execute a
Lake build, monitor its progress, and await the result.
-/

open System

namespace Lake

/-- Unicode icons that make up the spinner in animation order. -/
def Monitor.spinnerFrames :=
  #['⣾','⣷','⣯','⣟','⡿','⢿','⣻','⣽']

/-- Context of the Lake build monitor. -/
structure MonitorContext where
  jobs : JobQueue
  out : IO.FS.Stream
  outLv : LogLevel
  failLv : LogLevel
  minAction : JobAction
  showOptional : Bool
  useAnsi : Bool
  showProgress : Bool
  showTime : Bool
  /-- How often to poll jobs (in milliseconds). -/
  updateFrequency : Nat
  /-- Whether to set `cancelTk?` on the first required target failure (`--fail-fast`). -/
  failFast : Bool := false
  /-- The build's cancellation token, if any. -/
  cancelTk? : Option IO.CancelToken := none
  /-- A returned target job can register more jobs after the outer fetch completes.
  Its lifetime keeps the monitor open without adding another reported job. -/
  until? : Option (Task Unit) := none

@[inline, instance_reducible] def MonitorContext.logger (ctx : MonitorContext) : MonadLog BaseIO :=
  .stream ctx.out ctx.outLv ctx.useAnsi

/-- State of the Lake build monitor. -/
structure MonitorState where
  jobNo : Nat := 0
  totalJobs : Nat := 0
  wantsRebuild : Bool := false
  failures : Array String
  resetCtrl : String
  lastUpdate : Nat
  spinnerIdx : Fin Monitor.spinnerFrames.size := ⟨0, by decide⟩

/-- Monad of the Lake build monitor. -/
abbrev MonitorM := ReaderT MonitorContext <| StateT MonitorState BaseIO

@[inline] def MonitorM.run
  (ctx : MonitorContext) (s : MonitorState) (self : MonitorM α)
: BaseIO (α × MonitorState) :=
  StateT.run (ReaderT.run self ctx) s

/--
The ANSI escape sequence for clearing the current line
and resetting the cursor back to the start.
-/
def Ansi.resetLine : String :=
  "\x1B[2K\r"

/-- Like `IO.FS.Stream.flush`, but ignores errors. -/
@[inline] def flush (out : IO.FS.Stream) : BaseIO PUnit :=
  out.flush |>.catchExceptions fun _ => pure ()

/-- Like `IO.FS.Stream.putStr`, but panics on errors. -/
@[inline] def print! (out : IO.FS.Stream) (s : String) : BaseIO PUnit :=
  out.putStr s |>.catchExceptions fun e =>
    panic! s!"[{decl_name%} failed: {e}] {repr s}"

namespace Monitor

@[inline] def print (s : String) : MonitorM PUnit := do
  print! (← read).out s

@[inline] nonrec def flush : MonitorM PUnit := do
  flush (← read).out

def renderProgress
  (running unfinished : Array OpaqueJob) (h : 0 < unfinished.size)
: MonitorM PUnit := do
  let {jobNo, totalJobs, ..} ← get
  let {useAnsi, showProgress, ..} ← read
  if showProgress ∧ useAnsi then
    let spinnerIcon ← modifyGet fun s =>
        (spinnerFrames[s.spinnerIdx], {s with spinnerIdx := s.spinnerIdx + ⟨1, by decide⟩})
    let resetCtrl ← modifyGet fun s => (s.resetCtrl, {s with resetCtrl := Ansi.resetLine})
    let caption :=
      -- Prefer the newest running job.
      -- This avoids the monitor focusing too long on any one job.
      -- (e.g., "Running job computation")
      if _ : 0 < running.size then
        s!"Running {running[running.size - 1].caption} (+ {running.size - 1} more)"
      else
        s!"Running {unfinished[unfinished.size - 1].caption}"
    print s!"{resetCtrl}{spinnerIcon} [{jobNo}/{totalJobs}] {caption}"
    flush

def reportJob (job : OpaqueJob) : MonitorM PUnit := do
  let {jobNo, totalJobs, ..} ← get
  let {failLv, outLv, showOptional, out, useAnsi, showProgress, minAction, showTime, ..} ← read
  let {task, caption, optional, ..} := job
  let {log, action, wantsRebuild, canceled, buildTime, ..} := task.get.state
  let maxLv := log.maxLv
  let failed := strictAnd log.hasEntries (maxLv ≥ failLv)
  let canceled := canceled && !failed
  if wantsRebuild then
    modify fun s => if s.wantsRebuild then s else {s with wantsRebuild := true}
  if failed && !optional then
    modify fun s => {s with failures := s.failures.push caption}
  let hasOutput := failed || (log.hasEntries && maxLv ≥ outLv)
  let showJob :=
    (!optional || showOptional) &&
    (hasOutput || canceled || (showProgress && !useAnsi && action ≥ minAction))
  if showJob then
    let verb := if canceled then "Canceled" else action.verb failed
    let icon := if hasOutput then maxLv.icon else if canceled then '⊘' else '✔'
    let opt := if optional then " (Optional)" else ""
    let time := if showTime && buildTime > 0 then s!" ({formatTime buildTime})" else ""
    let caption := s!"{icon} [{jobNo}/{totalJobs}]{opt} {verb} {caption}{time}"
    let caption :=
      if useAnsi then
        let color := if hasOutput then maxLv.ansiColor else if canceled then "33" else "32"
        Ansi.chalk color caption
      else
        caption
    let resetCtrl ← modifyGet fun s => (s.resetCtrl, {s with resetCtrl := ""})
    print s!"{resetCtrl}{caption}\n"
    if hasOutput then
      let outLv := if failed then .trace else outLv
      log.replay (logger := .stream out outLv useAnsi)
    flush
where
  formatTime ms :=
    if ms > 10000 then s!"{ms / 1000}s"
    else if ms > 1000 then s!"{(ms) / 1000}.{(ms+50) / 100 % 10}s"
    else s!"{ms}ms"

def drainQueue : MonitorM (Array OpaqueJob) := do
  let newJobs ← (← read).jobs.modifyGet ((·, #[]))
  modify fun s => {s with totalJobs := s.totalJobs + newJobs.size}
  return newJobs

def scanJobs (new unfinished : Array OpaqueJob) : MonitorM (Array OpaqueJob × Array OpaqueJob) := do
  let pollJobs := fun (running, unfinished) job => do
    match (← IO.getTaskState job.task) with
    | .finished =>
      reportJob job
      modify fun s => {s with jobNo := s.jobNo + 1}
      return (running, unfinished)
    | .running =>
      return (running.push job, unfinished.push job)
    | .waiting =>
      return (running, unfinished.push job)
  let r ← unfinished.foldlM pollJobs (#[], #[])
  new.foldlM pollJobs r

def sleep : MonitorM PUnit := do
  let now ← IO.monoMsNow
  let lastUpdate := (← get).lastUpdate
  let sleepTime : Nat := (← read).updateFrequency - (now - lastUpdate)
  if sleepTime > 0 then
    IO.sleep sleepTime.toUInt32
  let now ← IO.monoMsNow
  modify fun s => {s with lastUpdate := now}

partial def loop
  (new unfinished : Array OpaqueJob)
: MonitorM PUnit := do
  let (running, unfinished) ← scanJobs new unfinished
  let ctx ← read
  if ctx.failFast then
    if let some tk := ctx.cancelTk? then
      unless (← get).failures.isEmpty do
        tk.set
  if h : 0 < unfinished.size then
    renderProgress running unfinished h
    sleep
    let new ← drainQueue
    loop new unfinished
  else
    -- Check the producer before the final drain. If it is done, every job it
    -- registered is now visible. Keep polling while an unregistered target is live.
    let pending ← match ctx.until? with
      | none => pure false
      | some t => Bool.not <$> IO.hasFinished t
    let new ← drainQueue
    if 0 < new.size then
      loop new unfinished
    else if pending then
      sleep
      loop (← drainQueue) unfinished

def main (init : Array OpaqueJob) : MonitorM PUnit := do
  let new ← drainQueue
  loop new init
  let resetCtrl ← modifyGet fun s => (s.resetCtrl, {s with resetCtrl := ""})
  unless resetCtrl.isEmpty do
    print resetCtrl
    flush

end Monitor

/-- **For internal use only.** -/
public structure MonitorResult where
  wantsRebuild : Bool
  failures : Array String
  numJobs : Nat

@[inline] def MonitorResult.isOk (self : MonitorResult) : Bool :=
  self.failures.isEmpty

def mkMonitorContext
  (cfg : BuildConfig) (jobs : JobQueue)
  (cancelTk? : Option IO.CancelToken := none)
: BaseIO MonitorContext := do
  let out ← cfg.out.get
  let useAnsi ← cfg.ansiMode.isEnabled out
  let outLv := cfg.outLv
  let failLv := cfg.failLv
  let isVerbose := cfg.verbosity = .verbose
  let showProgress := cfg.showProgress
  let minAction := if isVerbose then .unknown else .unpack
  let showOptional := isVerbose
  let showTime := isVerbose || !useAnsi
  let updateFrequency := 100
  return {
    jobs, out, failLv, outLv, minAction, showOptional
    useAnsi, showProgress, showTime, updateFrequency, cancelTk?
    failFast := cfg.failFast
  }

def monitorJobs'
  (ctx : MonitorContext)
  (initJobs : Array OpaqueJob)
  (initFailures : Array String := #[])
  (resetCtrl : String := "")
: BaseIO MonitorResult := do
  let s := {
    resetCtrl
    lastUpdate := ← IO.monoMsNow
    failures := initFailures
  }
  let (_,s) ← Monitor.main initJobs |>.run ctx s
  return {
    failures := s.failures
    numJobs := s.totalJobs
    wantsRebuild := s.wantsRebuild
  }

/-- The job monitor function. An auxiliary definition for `runFetchM`. -/
@[inline, deprecated "Deprecated without replacement." (since := "2025-01-08")]
public def monitorJobs
  (initJobs : Array OpaqueJob)
  (jobs : IO.Ref (Array OpaqueJob))
  (out : IO.FS.Stream)
  (failLv outLv : LogLevel)
  (minAction : JobAction)
  (showOptional useAnsi showProgress showTime : Bool)
  (resetCtrl : String := "")
  (initFailures : Array String := #[])
  (updateFrequency := 100)
: BaseIO MonitorResult := do
  let ctx := {
    jobs, out, failLv, outLv, minAction, showOptional
    useAnsi, showProgress, showTime, updateFrequency
  }
  monitorJobs' ctx initJobs initFailures resetCtrl

/-- Exit code to return if `--no-build` is set and a build is required. -/
public def noBuildCode : ExitCode := 3

def BuildContext.saveOutputs
  [logger : MonadLog BaseIO] (bctx : BuildContext) (out : IO.FS.Stream) (outputsFile : FilePath)
: BaseIO Unit := do
  let some ref := bctx.outputsRef?
    | print! out "Build missing input-to-output mappings. (This is likely a bug in Lake.)\n"
      return
  let ws := bctx.workspace
  -- TODO: Carry proof index is in bounds in `BuildContext` when its workspace is non-opaque.
  let some pkg := ws.packages[bctx.outputsIdx]?
    | print! out "Tracked package not found. (This is likely a bug in Lake.)\n"
      return
  have : MonadWorkspace Id := ⟨ws⟩
  unless Id.run pkg.isArtifactCacheWritable do
    logWarning s!"{pkg.prettyName}: \
      the artifact cache is not enabled for this package, so the artifacts described \
      by the mappings produced by `-o` will not necessarily be available in the cache."
  let isVerbose := bctx.verbosity matches .verbose
  match (← (← ref.get).writeFile outputsFile pkg.isPlatformIndependent ∅) with
  | .ok _ log =>
    if !log.isEmpty && isVerbose then
      print! out "There were issues saving input-to-output mappings from the build:\n"
      log.replay
  | .error _ log =>
    print! out "Failed to save input-to-output mappings from the build.\n"
    if isVerbose then
      log.replay

def reportResult (cfg : BuildConfig) (out : IO.FS.Stream) (result : MonitorResult) : BaseIO Unit := do
  if result.failures.isEmpty then
    if cfg.showProgress && cfg.showSuccess then
      let numJobs := result.numJobs
      if numJobs == 0 then
        print! out "Nothing to build.\n"
      else
        let jobs := if numJobs == 1 then "1 job" else s!"{numJobs} jobs"
        if cfg.noBuild then
          print! out s!"All targets up-to-date ({jobs}).\n"
        else
          print! out s!"Build completed successfully ({jobs}).\n"
  else
    print! out "Some required targets logged failures:\n"
    result.failures.forM (print! out s!"- {·}\n")
    flush out

structure BuildResult (α : Type u) extends MonitorResult where
  out : Except String α

instance : CoeOut (BuildResult α) MonitorResult := ⟨BuildResult.toMonitorResult⟩

@[inline] def BuildResult.isOk (self : BuildResult α) : Bool :=
  self.out.isOk

def monitorJob (ctx : MonitorContext) (job : Job α) : BaseIO (BuildResult α) := do
  let result ← monitorJobs' ctx #[job]
  if result.isOk then
    if let some a ← job.wait? then
      return {toMonitorResult := result, out := .ok a}
    else
      -- Computation job failed but was unreported in the monitor. This should be impossible.
      return {toMonitorResult := result, out := .error <|
        "uncaught top-level build failure (this is likely a bug in Lake)"}
  else
    return {toMonitorResult := result, out := .error "build failed"}

def mkBuildContext
  (ws : Workspace) (cfg : BuildConfig) (jobs : JobQueue)
  (cancelTk? : Option IO.CancelToken := none)
: BaseIO BuildContext := return {
  opaqueWs := ws
  toBuildConfig := {cfg with
    macosxDeploymentTarget? := ← id do
      if System.Platform.isOSX then
        match cfg.macosxDeploymentTarget? with
        | some ver => return some ver
        | none =>
          -- TODO: Consider adding `MACOSX_DEPLOYMENT_TARGET` to `Lake.Env`
          return some <| (← IO.getEnv "MACOSX_DEPLOYMENT_TARGET").getD "99.0"
      else
        return cfg.macosxDeploymentTarget?
    }
  outputsRef? := ← id do
    if cfg.outputsFile?.isSome && cfg.outputsIdx < ws.packages.size then
      some <$> CacheRef.mk
    else
      return none
  registeredJobs := jobs
  leanTrace := .ofHash (pureHash ws.lakeEnv.leanGithash)
    s!"Lean {Lean.versionStringCore}, commit {ws.lakeEnv.leanGithash}"
  cancelTk?
  leanIncludeDirs := ← ws.packages.mapM fun pkg => do
    unless pkg.bootstrap do
      return none
    let dir := pkg.bootstrapIncludeDir
    let mut trace := BuildTrace.nil "Lean includes"
    -- Must be kept up-to-date with the files `lean.h` can include
    for header in #["lean.h", "config.h", "version.h", "mimalloc.h"] do
      let leanH := TextFilePath.mk <| dir / "lean" / header
      match ← (computeTrace (n := IO) leanH).toBaseIO with
      | .ok fileTrace =>
        trace := trace.mix fileTrace
      | .error (.noFileOrDirectory ..) =>
        -- some headers (e.g., `mimalloc.h`) are optional
        -- missing required headers will be caught during compilation
        continue
      | _ =>
        return none
    return some (dir, trace)
}

def Workspace.startBuild
  (bctx : BuildContext) (build : FetchM α) (caption := "job computation")
: BaseIO (Job α) := do
  let compute := Job.async build (caption := caption)
  let track ← PaperLean.SetupIndex.observesProviders bctx
  (PaperLean.runFetchFor track compute).run'.run bctx |>.run nilTrace

def finalizeBuild
  (cfg : BuildConfig) (bctx : BuildContext) (mctx : MonitorContext) (result : BuildResult α)
: IO α := do
  if result.isOk || !result.failures.isEmpty then reportResult cfg mctx.out result
  if let some outputsFile := cfg.outputsFile? then
    bctx.saveOutputs (logger := mctx.logger) mctx.out outputsFile
  match result.out with
  | .ok a =>
    return a
  | .error e =>
    if cfg.noBuild && result.wantsRebuild then
      IO.Process.exit noBuildCode.toUInt8
    else
      throw (IO.userError e)

/-- All three public runners bracket the same resources. Passive queries register their
own context without enabling build accelerators, even when invoked inside another run. -/
private def withPaperLeanBuildState (ws : Workspace) (ctx : BuildContext) (enable : Bool)
    (act : BaseIO α) : BaseIO α := do
  let compile := enable && !ctx.noBuild
  let scheduler ← PaperLean.Schedule.startFor ctx ws.dir compile
  PaperLean.BuildData.startFor ctx ws.dir compile
  PaperLean.HashCache.startFor ctx ws.dir enable
  PaperLean.SetupIndex.beginRun ctx ws enable
  try PaperLean.SourceInputScope.withRun ctx enable act finally
    PaperLean.SetupIndex.endRun ctx
    PaperLean.BuildData.finishFor ctx
    PaperLean.HashCache.finishFor ctx
    PaperLean.Schedule.finishFor ctx scheduler

/--
Run a build function in the Workspace's context using the provided configuration.
Reports incremental build progress and build logs. In quiet mode, only reports
failing build jobs (e.g., when using `-q` or non-verbose `--no-build`).
-/
public def Workspace.runFetchM
  (ws : Workspace) (build : FetchM α) (cfg : BuildConfig := {}) (caption := "job computation")
: IO α := do
  let jobs ← mkJobQueue
  let cancelTk? ← if cfg.failFast then some <$> IO.CancelToken.new else pure none
  let mctx ← mkMonitorContext cfg jobs cancelTk?
  let bctx ← mkBuildContext ws cfg jobs cancelTk?
  let result ← withPaperLeanBuildState ws bctx false do
    let job ← startBuild bctx build caption
    monitorJob mctx job
  finalizeBuild cfg bctx mctx result

def monitorBuild (mctx : MonitorContext) (job : Job (Job α)) : BaseIO (BuildResult α) := do
  let loggedFailure := fun (state : JobState) => state.log.hasEntries && state.log.maxLv ≥ mctx.failLv
  let cancel := fun (optional : Bool) => do
    if mctx.failFast && !optional then mctx.cancelTk?.forM (·.set)
  let lifetime ← BaseIO.bindTask job.task (sync := true) fun
    | .ok target _ => BaseIO.mapTask (t := target.task) (sync := true) fun result => do
      if (result matches .error ..) || loggedFailure result.state then cancel target.optional
    | .error .. => do cancel job.optional; return .pure ()
  let result ← monitorJob {mctx with until? := some lifetime} job
  match result.out with
  | .ok target =>
    let outcome ← target.wait
    let state := outcome.state
    let result := {result with wantsRebuild := result.wantsRebuild || state.wantsRebuild}
    -- A registered required failure was already reported by the monitor. An unregistered
    -- returned target still uses the same log threshold, even if it returned a value.
    if !target.optional && loggedFailure state then
      state.log.replay (logger := .stream mctx.out .trace mctx.useAnsi)
      let caption := if target.caption.isEmpty then "top-level target" else target.caption
      return {result with failures := #[caption], out := .error "build failed"}
    match outcome with
    | .ok a _ => return {result with out := .ok a}
    | .error .. => return {result with out := .error <|
        "uncaught top-level build failure (this is likely a bug in the build script)"}
  | .error e =>
    return {result with out := .error e}

/--
Returns whether a build is needed to validate `build`. Does not report on the attempted build.

This is equivalent to checking whether `lake build --no-build` exits with code 0.
-/
public def Workspace.checkNoBuild
  (ws : Workspace) (build : FetchM (Job α))
: BaseIO Bool := do
  let jobs ← mkJobQueue
  let cfg := {noBuild := true}
  let mctx ← mkMonitorContext cfg jobs
  let bctx ← mkBuildContext ws cfg jobs
  let result ← withPaperLeanBuildState ws bctx false do
    let job ← startBuild bctx build
    monitorBuild mctx job
  return result.isOk -- `isOk` means no failures, and thus no `--no-build` failures

/-- Run a build function in the Workspace's context and await the result. -/
-- PaperLean: (not inlined: its body calls PaperLean's code)
@[noinline] public def Workspace.runBuild
  (ws : Workspace) (build : FetchM (Job α)) (cfg : BuildConfig := {})
: IO α := do
  let jobs ← mkJobQueue
  let cancelTk? ← if cfg.failFast then some <$> IO.CancelToken.new else pure none
  let mctx ← mkMonitorContext cfg jobs cancelTk?
  let bctx ← mkBuildContext ws cfg jobs cancelTk?
  let result ← withPaperLeanBuildState ws bctx true do
    let job ← startBuild bctx build
    monitorBuild mctx job
  finalizeBuild cfg bctx mctx result

/-- Produce a build job in the Lake monad's workspace and await the result. -/
@[inline] public def runBuild
  (build : FetchM (Job α)) (cfg : BuildConfig := {})
: LakeT IO α := do (← getWorkspace).runBuild build cfg
-- Modified by PaperLean.
