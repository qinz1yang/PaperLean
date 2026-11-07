/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone, Siddharth Bhat
-/
module

prelude
public import Lake.Util.Log
import Lake.Util.Proc
import Lake.Util.FilePath
import Lake.Util.IO
import Lake.Util.Url
import Init.Data.String.Search
import Init.Data.String.TakeDrop
import Init.System.Platform
import Lean.CoreM
import Lean.Compiler.Options
import Lake.PaperLean.BuildEnv
import Lake.PaperLean.Env

/-! # Common Build Actions
Low level actions to build common Lean artifacts via the Lean toolchain.
-/

open System
open Lean hiding SearchPath

namespace Lake

/-- Each accelerated compiler invocation owns its input through both Lean and leanir.
Concurrent invocations may replace the display file for the same module. -/
private def withChildSetup (launchDir : BaseIO (Option FilePath)) (file : FilePath)
    (setup : ModuleSetup) (run : FilePath → FilePath → LogIO Unit) : LogIO Unit := do
  unless ← PaperLean.accelerated do
    IO.FS.writeFile file (toJson setup).pretty
    return ← run file file
  let side := file.withExtension "paperlean"
  let compactText := (PaperLean.setupToJsonCompact setup).compress
  let compact ← if PaperLean.SetupIndex.refersToIndex setup then pure true
    else PaperLean.writeSideFile side compactText
  let (display, text) ← if compact then pure (side, compactText) else do
    let text := (toJson setup).pretty
    PaperLean.publishFile file (·.putStr text)
    pure (file, text)
  if let some dir ← launchDir then
    let path := dir / s!"launch-{← PaperLean.freshGeneration}.paperlean"
    let written ← (do IO.FS.createDirAll dir; PaperLean.writeNewFile path (·.putStr text)).toBaseIO
    if let .ok true := written then
      try return ← run path display finally discard <| (IO.FS.removeFile path).toBaseIO
  -- Standalone callers and workspaces that cannot write a generation directory
  -- still use an exclusively created file for this invocation.
  IO.FS.withTempFile fun h path => do
    h.putStr text
    h.flush
    run path display

-- PaperLean: (not inlined: its body calls PaperLean's code)
@[noinline] public def compileLeanModuleForBuild
  (childEnv : BaseIO (Array (String × Option String)))
  (launchDir : BaseIO (Option FilePath))
  (leanFile relLeanFile : FilePath)
  (setup : ModuleSetup) (setupFile : FilePath)
  (arts : ModuleArtifacts)
  (leanArgs : Array String := #[])
  (leanPath : SearchPath := [])
  (lean : FilePath := "lean")
  (leanir : FilePath := "leanir")
: LogIO Unit := do
  let mut args := leanArgs.push leanFile.toString
  if let some oleanFile := arts.olean? then
    createParentDirs oleanFile
    args := args ++ #["-o", oleanFile.toString]
  if let some ileanFile := arts.ilean? then
    createParentDirs ileanFile
    args := args ++ #["-i", ileanFile.toString]
  let opts := setup.options.toOptions
  let postponeCompile := setup.isModule && Compiler.compiler.postponeCompile.get opts
  if !postponeCompile then
    if let some cFile := arts.c? then
      createParentDirs cFile
      args := args ++ #["-c", cFile.toString]
  if let some bcFile := arts.bc? then
    createParentDirs bcFile
    args := args ++ #["-b", bcFile.toString]
  createParentDirs setupFile
  args := args ++ #["--setup", setupFile.toString]
  args := args.push "--json"
  withChildSetup launchDir setupFile setup fun setupPath displayPath => do
  withLogErrorPos do
  let spawnArgs : IO.Process.SpawnArgs := {
    args
    cmd := lean.toString
    env := #[
      ("LEAN_PATH", leanPath.toString)
    ]
  }
  -- PaperLean: with the olean packs written so far during the build (`Lake.PaperLean.BuildData`),
  -- which the logged command leaves out, so that the log that the trace records is Lake's
  logVerbose (mkCmdLog spawnArgs)
  let out ← rawProc (quiet := true) { spawnArgs with
    args := args.set! (args.size - 2) setupPath.toString
    env := spawnArgs.env ++ (← childEnv) }
  let outLogPos ← getLogPos
  unless out.stdout.isEmpty do
    let txt ← out.stdout.split '\n' |>.foldM (init := "") fun (txt : String) ln => do
      let ln := ln.copy
      if let .ok (msg : SerialMessage) := Json.parse ln >>= fromJson? then
        unless txt.isEmpty do
          logInfo s!"stdout:\n{txt}"
        let msg := {msg with fileName := mkRelPathString relLeanFile}
        logSerialMessage msg
        return txt
      else if txt.isEmpty && ln.isEmpty then
        return txt
      else
        return txt ++ ln ++ "\n"
    unless txt.isEmpty do
      logInfo s!"stdout:\n{txt}"
  unless out.stderr.isEmpty do
    logInfo s!"stderr:\n{out.stderr.trimAscii}"
  -- Elide the generic "Lean exited with code 1" when Lean already
  -- reported errors (the usual compiler-failure case). Keep it for other
  -- nonzero codes, for code 1 without diagnostics, and for the anomalous
  -- case where Lean logs errors but exits successfully.
  -- See https://github.com/leanprover/lean4/issues/10825
  let hasErrors := (← getLog).takeFrom outLogPos |>.any (·.level matches .error)
  if out.exitCode = 1 && hasErrors then
    failure
  else if out.exitCode ≠ 0 || hasErrors then
    error s!"Lean exited with code {out.exitCode}"
  if postponeCompile then
    if let (some irFile, some cFile) := (arts.ir?, arts.c?) then
      createParentDirs irFile
      createParentDirs cFile
      try
        let irArgs : IO.Process.SpawnArgs := {
          cmd := leanir.toString
          args := #[displayPath.toString, irFile.toString, cFile.toString]
          env := #[("LEAN_PATH", leanPath.toString)]
        }
        if setupPath == displayPath then
          proc irArgs
        else
          logVerbose (mkCmdLog irArgs)
          let out ← rawProc (quiet := true) { irArgs with args := irArgs.args.set! 0 setupPath.toString }
          logOutput out logInfo
          if out.exitCode != 0 then
            error s!"external command '{irArgs.cmd}' exited with code {out.exitCode}"
      catch e =>
        if let some oleanFile := arts.olean? then
          removeFileIfExists oleanFile
        throw e

@[noinline] public def compileLeanModule
  (leanFile relLeanFile : FilePath)
  (setup : ModuleSetup) (setupFile : FilePath)
  (arts : ModuleArtifacts)
  (leanArgs : Array String := #[])
  (leanPath : SearchPath := [])
  (lean : FilePath := "lean")
  (leanir : FilePath := "leanir")
: LogIO Unit :=
  compileLeanModuleForBuild PaperLean.BuildEnv.leanEnv (pure none) leanFile relLeanFile setup setupFile arts
    leanArgs leanPath lean leanir

public def compileO
  (oFile srcFile : FilePath)
  (moreArgs : Array String := #[]) (compiler : FilePath := "cc")
: LogIO Unit := do
  createParentDirs oFile
  proc {
    cmd := compiler.toString
    args := #["-c", "-o", oFile.toString, srcFile.toString] ++ moreArgs
  }

public def mkArgs (basePath : FilePath) (args : Array String) : LogIO (Array String) := do
  -- Use response file to avoid potentially exceeding CLI length limits.
  -- On Windows this is always needed; on macOS/Linux this is needed for large
  -- projects like Mathlib where the number of object files exceeds ARG_MAX.
  let rspFile := basePath.addExtension "rsp"
  let h ← IO.FS.Handle.mk rspFile .write
  args.forM fun arg =>
    -- Escape special characters
    let arg := arg.foldl (init := "") fun s c =>
      if c == '\\' || c == '"' then
        s.push '\\' |>.push c
      else
        s.push c
    h.putStr s!"\"{arg}\"\n"
  return #[s!"@{rspFile}"]

public def compileStaticLib
  (libFile : FilePath) (oFiles : Array FilePath)
  (ar : FilePath := "ar") (thin := false)
: LogIO Unit := do
  createParentDirs libFile
  -- `ar rcs` does not remove old files from the archive, so it must be deleted first
  removeFileIfExists libFile
  let args := #["rcs"]
  let args := if thin then args.push "--thin" else args
  let args := args.push libFile.toString ++ (← mkArgs libFile <| oFiles.map toString)
  proc {cmd := ar.toString, args}

public def compileSharedLib
  (libFile : FilePath) (linkArgs : Array String)
  (linker : FilePath := "cc") (macosxDeploymentTarget? : Option String := none)
: LogIO Unit := do
  createParentDirs libFile
  proc {
    cmd := linker.toString
    args := #["-shared", "-o", libFile.toString] ++ (← mkArgs libFile linkArgs)
    -- See `BuildConfig.macosxDeploymentTarget?` for details
    env := macosxDeploymentTarget?.elim #[] fun ver => #[("MACOSX_DEPLOYMENT_TARGET", some ver)]
  }

public def compileExe
  (binFile : FilePath) (linkArgs : Array String)
  (linker : FilePath := "cc") (macosxDeploymentTarget? : Option String := none)
: LogIO Unit := do
  createParentDirs binFile
  proc {
    cmd := linker.toString
    args := #["-o", binFile.toString] ++ (← mkArgs binFile linkArgs)
    -- See `BuildConfig.macosxDeploymentTarget?` for details
    env :=  macosxDeploymentTarget?.elim #[] fun ver => #[("MACOSX_DEPLOYMENT_TARGET", some ver)]
  }

/-- Download a file using `curl`, clobbering any existing file. -/
public def download
  (url : String) (file : FilePath) (headers : Array String := #[])
: LogIO PUnit := do
  if (← file.pathExists) then
    IO.FS.removeFile file
  else
    createParentDirs file
  let args := #["-s", "-S", "-f", "-o", file.toString, "-L", url]
  let args := headers.foldl (init := args) (· ++ #["-H", ·])
  proc (quiet := true) {cmd := ← Internal.getCurl, args}

/-- Unpack an archive `file` using `tar` into the directory `dir`. -/
public def untar (file : FilePath) (dir : FilePath) (gzip := true) : LogIO PUnit := do
  IO.FS.createDirAll dir
  let mut opts := "-xvv"
  if gzip then
    opts := opts.push 'z'
  proc (quiet := true) {
    cmd := "tar",
    args := #[opts, "-f", file.toString, "-C", dir.toString]
  }

/-- Pack a directory `dir` using `tar` into the archive `file`. -/
public def tar
  (dir : FilePath) (file : FilePath)
  (gzip := true) (excludePaths : Array FilePath := #[])
: LogIO PUnit := do
  createParentDirs file
  let mut args := #["-cvv"]
  if gzip then
    args := args.push "-z"
  for path in excludePaths do
    args := args.push s!"--exclude={path}"
  proc (quiet := true) {
    cmd := "tar"
    args := args ++ #["-f", file.toString, "-C", dir.toString, "."]
    -- don't pack `._` files on MacOS
    env := if Platform.isOSX then #[("COPYFILE_DISABLE", "true")] else #[]
  }
-- Modified by PaperLean.
