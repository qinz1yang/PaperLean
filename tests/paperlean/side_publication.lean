/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.PaperLean.ImportState
import Lean.PaperLean.NativeLibs
import Lean.PaperLean.OLeanPack
import Lean.Environment
import Lean.Util.Path

open System Lean Lean.PaperLean

private def require (p : Bool) (msg : String) : IO Unit := unless p do throw <| IO.userError msg

private def write (kind : String) (out lib : FilePath) : IO Unit := do
  if kind == "image" then
    discard <| writeImportImage out
  else
    discard <| writeNativeManifestFiles out.toString lib.toString #[] #[] #[]

private def regularMode (out : FilePath) : IO Unit := do
  let s ← IO.Process.run {cmd := "python3", args := #["-c",
    "import os,sys; print(os.stat(sys.argv[1]).st_mode & 0o222)", out.toString]}
  require (s.trimAscii.copy == "0") "import image is writable"
  require (← OLeanPack.verifyImportImage out.toString).isEmpty "invalid published import image"

private def classify (kind mode : String) (dir : FilePath) : IO Unit := do
  let lib := dir / "lib"
  IO.FS.writeFile lib "lib"
  let out := dir / "out"
  let pid ← IO.Process.getPID
  let legacy := if kind == "image" then out.addExtension s!"tmp.{pid}" else out.addExtension "tmp"
  let sentinel := dir / "sentinel"
  IO.FS.writeFile sentinel "untouched"
  if mode == "nul" then
    IO.FS.writeFile out "keep"
    let bad := FilePath.mk (out.toString ++ String.singleton (Char.ofNat 0) ++ "suffix")
    require ((← (write kind bad lib).toBaseIO) matches .error ..) "accepted a truncated output path"
    require ((← IO.FS.readFile out) == "keep") "NUL-truncated pathname was overwritten"
    return
  let paths := #[legacy] ++ (Array.range 3).map fun i => out.addExtension s!"tmp.{pid}-{i}"
  let mut types := #[]
  for path in paths do
    if mode == "hard" then IO.FS.hardLink sentinel path
    else if mode == "symlink" then
      discard <| IO.Process.run {cmd := "ln", args := #["-s", sentinel.toString, path.toString]}
    else if mode == "fifo" then discard <| IO.Process.run {cmd := "mkfifo", args := #[path.toString]}
    else throw (IO.userError "unknown sentinel mode")
    types := types.push (← path.symlinkMetadata).type
  write kind out lib
  require ((← IO.FS.readBinFile sentinel) == "untouched".toUTF8) "unrelated file was overwritten"
  for (path, ty) in paths.zip types do
    require ((← path.symlinkMetadata).type == ty) "unrelated temporary name changed"
  if kind == "image" then regularMode out
  else
    require ((← IO.FS.readBinFile out).size > 0) "empty manifest"
    discard <| IO.Process.run {cmd := "python3", args := #["-c",
      "import os, sys; assert os.stat(sys.argv[1]).st_mode == os.stat(sys.argv[2]).st_mode",
      out.toString, lib.toString]}

private def race (kind : String) (dir : FilePath) : IO Unit := do
  let out := dir / "out"
  let mut libs := #[]
  let mut valid := #[]
  for i in [:8] do
    let lib := dir / s!"lib-{i}"
    let ref := dir / s!"ref-{i}"
    IO.FS.writeFile lib s!"library {i}"
    libs := libs.push lib
    if kind == "manifest" then
      write kind ref lib
      valid := valid.push (← IO.FS.readBinFile ref)
  let barrier : IO.Promise Unit ← IO.Promise.new
  let mut tasks := #[]
  for lib in libs do
    tasks := tasks.push (← IO.asTask (prio := .dedicated) do
      discard <| IO.wait barrier.result?
      for _ in [:4] do write kind out lib)
  barrier.resolve ()
  for task in tasks do discard <| IO.ofExcept (← IO.wait task)
  if kind == "image" then regularMode out
  else
    let final ← IO.FS.readBinFile out
    require (valid.any (· == final)) "final manifest combines different publications"
  let files ← dir.readDir
  require (!(files.any (·.fileName.startsWith "out.tmp"))) "retained an owned temporary"
  -- Failing at the final rename must retire only files created by this invocation.
  let bad := dir / "fail"
  IO.FS.createDirAll bad
  IO.FS.writeFile (bad / "saved") "keep"
  let r ← (write kind bad libs[0]!).toBaseIO
  require (r matches .error ..) "unexpected successful replacement of a nonempty directory"
  require ((← IO.FS.readFile (bad / "saved")) == "keep") "lost file at failed destination"
  require (!(← dir.readDir).any (·.fileName.startsWith "fail.tmp")) "leaked failed writer temporary"

def main (args : List String) : IO Unit := do
  match args with
  | ["pack", dir, file] => discard <| OLeanPack.create #[dir] file
  | [kind, mode, path] => do
    let dir := FilePath.mk path
    IO.FS.createDirAll dir
    if kind == "image" then
      initSearchPath (← findSysroot)
      discard <| importModules #[{module := `PubTiny}] {}
    if mode == "race" then race kind dir else classify kind mode dir
    IO.println s!"{kind} {mode} passed"
  | _ => throw (IO.userError "expected pack or writer arguments")
