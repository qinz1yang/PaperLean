/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.System.IO

open System

set_option doc.verso true

namespace Lake

/-- Creates any missing parent directories of {lean}`path`. -/
public def createParentDirs (path : FilePath) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir

/-- Remove the file at {lean}`path` if it exists. -/
public def removeFileIfExists (path : FilePath) : IO Unit := do
  try IO.FS.removeFile path catch
    | .noFileOrDirectory .. => pure ()
    | e => throw e

/- Publish `tmp` at `path` unless `path` already exists; `false` if the file system cannot link it. -/
private def linkIfNew (tmp path : FilePath) : IO Bool := do
  try IO.FS.hardLink tmp path; return true
  catch
    | .alreadyExists .. => return true
    | _ => return false

/-
Write `content` to a fresh temporary file next to `path`, flush it, and then
publish it at `path` with an atomic hard link.  The link preserves the
"do nothing if the file already exists" behaviour while ensuring that readers
never observe a partially written file at `path`.
-/
private def writeNewFileAtomically
  (path : FilePath) (write : IO.FS.Handle → IO Unit) : IO Unit := do
  if (← path.pathExists) then return
  let dir := path.parent.getD "."
  let tmpName := "." ++ path.fileName.getD "tmp" ++ "." ++ toString (← IO.Process.getPID) ++
    "." ++ toString (← IO.monoNanosNow) ++ ".tmp"
  let tmp := dir / tmpName
  let mut linked := false
  try
    IO.FS.withFile tmp .writeNew (fun h => do
      write h
      h.flush)
    linked ← linkIfNew tmp path
  catch _ =>
    pure ()
  try IO.FS.removeFile tmp catch _ => pure ()
  unless linked do
    -- (where a temporary file next to `path` or a hard link is not possible: the former direct write)
    let h ← try IO.FS.Handle.mk path IO.FS.Mode.writeNew catch
      | .alreadyExists .. => return
      | e => throw e
    write h

/--
Write the UTF-8 encoded string {lean}`content` to {lean}`path`.
If the file already exists, does nothing.
-/
public def writeFileIfNew (path : FilePath) (content : String) : IO Unit :=
  writeNewFileAtomically path fun h => h.putStr content

/--
Write the bytes of {lean}`content` to {lean}`path`.
If the file already exists, does nothing.
-/
public def writeBinFileIfNew (path : FilePath) (content : ByteArray) : IO Unit :=
  writeNewFileAtomically path fun h => h.write content

/--
Remove a directory and all its contents.
Like {lean}`IO.FS.removeDirAll`, but does not fail if {lean}`path` does not exist
or if a file is first deleted by a racing process.
-/
public partial def removeDirAllIfExists (path : FilePath) : IO Unit := do
  let ents ← try path.readDir catch
    | .noFileOrDirectory .. => return -- path did not exist or something else was faster
    | e => throw e
  for ent in ents do
    -- Do not follow symlinks
    let mdata ← try ent.path.symlinkMetadata catch
      | .noFileOrDirectory .. => continue -- something else was faster
      | e => throw e
    if mdata.type == .dir then
      removeDirAllIfExists ent.path
    else
      removeFileIfExists ent.path
  try IO.FS.removeDir path catch
    | .noFileOrDirectory .. => return -- something else was faster
    | e => throw e

/-- Copy a file from {lean}`src` to {lean}`dst`. -/
public def copyFile (src dst : FilePath) : IO Unit := do
  let contents ← IO.FS.readBinFile src
  IO.FS.writeBinFile dst contents

/-- Copy a directory and all its contents from {lean}`src` to {lean}`dst`. -/
public partial def copyDirAll (src dst : FilePath) : IO Unit := do
  IO.FS.createDirAll dst
  let ents ← src.readDir
  for ent in ents do
    let srcPath := src / ent.fileName
    let dstPath := dst / ent.fileName
    if (← srcPath.isDir) then
      copyDirAll srcPath dstPath
    else
      copyFile srcPath dstPath

/-- Returns the normalized real path of a file if it exists. Otherwise, returns {lean}`""`. -/
public def resolvePath (path : FilePath) : BaseIO FilePath := do
  match (← (IO.FS.realPath path).toBaseIO) with
  | .ok path =>
    -- Real path does not guarantee the file exists on Windows
    if (← path.pathExists) then
      return path.normalize
    else
      return ""
  | _ =>
    return ""

/-- Returns the normalized real path of a file if and only if it exists. -/
@[inline] public def resolvePath? (path : FilePath) : BaseIO (Option FilePath) := do
  let path ← resolvePath path
  return if path.toString.isEmpty then none else some path
