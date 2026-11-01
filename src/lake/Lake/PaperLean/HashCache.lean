/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lake.Build.Trace
import Init.While
import Lake.PaperLean.Env
import Lean.PaperLean.System
import Std.Data.HashMap.Basic

/-!
The `.hash` files that builds under `paperlean` commands read (`Lake.fetchFileHash`): Lake reads those
of every module that is up to date, seven per module, which take most of the time of a build that
compiles little. A build records the contents of those it read with their identities (device, inode,
size, modification and status change times: `Lean.PaperLean.fileIdentity`) in
`.lake/paperlean-hashes.paperlean`, and later builds take the contents from there instead of reading
a file whose identity is still that recorded, which one `stat` costs. A file is only recorded if it
was last changed well before the build started (`margin`, by the time of a file it writes then): any
later write changes its identity, even where file systems keep coarse times, and the status change
time cannot be set. The record holds only what the last build read; one that is missing, damaged, or
of another build is ignored, and so is the record of a file that changed since;
`PAPERLEAN_HASH_CACHE=0` turns it off.
-/

open System Lean

namespace Lake.PaperLean.HashCache

/-- A `.hash` file as recorded: its identity and the hash it holds. -/
structure Entry where
  identity : ByteArray
  hash : UInt64

/-- The record of the build. -/
structure Loaded where
  file : FilePath
  entries : Std.HashMap String Entry
  /-- Files last changed before this time (s since the epoch) are recorded. -/
  before : Int

private builtin_initialize loadedRef : IO.Ref (Option Loaded) ← IO.mkRef none

-- (Lists: an array that threads share is copied on every change.)

/-- The recorded files that this build took from the record. -/
private builtin_initialize hitsRef : IO.Ref (List String) ← IO.mkRef []

/-- The files read during the build that are recorded. -/
private builtin_initialize newRef : IO.Ref (List (String × Entry)) ← IO.mkRef []

/-- How long before the start of the build a file must have been last changed to be recorded (s). -/
private def margin : Int := 2

/-- The size of an identity (`Lean.PaperLean.fileIdentity`). -/
private def identitySize : Nat := 56

private def le (n : Nat) (x : UInt64) (out : ByteArray) : ByteArray := Id.run do
  let mut out := out
  for i in [0:n] do
    out := out.push (x >>> (8 * i).toUInt64).toUInt8
  return out

private def rd (b : ByteArray) (i n : Nat) : UInt64 := Id.run do
  let mut x : UInt64 := 0
  for j in [0:n] do
    x := x ||| (b.get! (i + j)).toUInt64 <<< (8 * j).toUInt64
  return x

/-- `s` padded with zeros to `n` bytes (cut if longer). -/
private def padded (s : String) (n : Nat) : ByteArray :=
  let b := s.toUTF8.extract 0 n
  b ++ ByteArray.mk (Array.replicate (n - b.size) 0)

/-- The header of a record, as that of PaperLean's side files (`src/paperlean/side_file.h`): magic,
kind, the version and build of PaperLean and Lean's commit that wrote it, and its size, followed by
the checksum of the entries. -/
private def headerOf : ByteArray :=
  padded "PAPERLEAN" 16 ++ padded "build-hashes" 16 ++
    padded s!"{Lean.PaperLean.version}+{Lean.PaperLean.build}" 64 ++ padded Lean.githash 40 |>
    le 4 (16 + 16 + 64 + 40 + 4 + 4 + 8) |> le 4 0

/-- The entries of a record, if this build wrote it and it is whole: after the header, each a path's
length (2 bytes) and bytes, its identity and its hash (8 bytes), little-endian. -/
private def decode (b : ByteArray) : Option (Std.HashMap String Entry) := Id.run do
  let h := headerOf
  if b.size < h.size + 8 || b.extract 0 h.size != h then return none
  let body := b.extract (h.size + 8) b.size
  if rd b h.size 8 != body.hash then return none
  let mut i := 0
  let mut out : Std.HashMap String Entry := {}
  while i < body.size do
    if i + 2 > body.size then return none
    let n := (rd body i 2).toNat
    let j := i + 2 + n
    if j + identitySize + 8 > body.size then return none
    let some path := String.fromUTF8? (body.extract (i + 2) j) | return none
    out := out.insert path
      { identity := body.extract j (j + identitySize), hash := rd body (j + identitySize) 8 }
    i := j + identitySize + 8
  return some out

private def encode (entries : Std.HashMap String Entry) : ByteArray :=
  let body := entries.fold (init := .empty) fun out path e =>
    let p := path.toUTF8
    if p.size ≥ 65536 || e.identity.size != identitySize then out else
    le 8 e.hash (le 2 p.size.toUInt64 out ++ p ++ e.identity)
  le 8 body.hash headerOf ++ body

/-- The modification and status change times (s) of an identity. -/
private def changeTimes (id : ByteArray) : Int × Int :=
  ((rd id 24 8).toInt64.toInt, (rd id 40 8).toInt64.toInt)

/-- The record of the workspace in `wsDir`. -/
public def recordFile (wsDir : FilePath) : FilePath := wsDir / ".lake" / "paperlean-hashes.paperlean"

/-- Starts using the record of the workspace in `wsDir`, at the start of a build under a `paperlean`
command (`accelerated`). -/
public def start (wsDir : FilePath) : BaseIO Unit := do
  loadedRef.set none
  hitsRef.set []
  newRef.set []
  unless ← accelerated do return
  if (← IO.getEnv "PAPERLEAN_HASH_CACHE") == some "0" then return
  let file := recordFile wsDir
  let r ← (do
    IO.FS.createDirAll (wsDir / ".lake")
    -- the file system's time now
    let clock := wsDir / ".lake" / "paperlean-clock.paperlean"
    if (← isSpecialFile clock) || (← isSpecialFile file) then return none
    IO.FS.writeFile clock ""
    let some id ← Lean.PaperLean.fileIdentity clock.toString | return none
    let (mt, ct) := changeTimes id
    let entries ← try pure ((decode (← IO.FS.readBinFile file)).getD {}) catch _ => pure {}
    return some { file, entries, before := min mt ct - margin : Loaded }).toBaseIO
  if let .ok (some l) := r then loadedRef.set (some l)

/-- The hash in the `.hash` file `hashFile`, as `Hash.load?` reads it, without reading the file if
it is recorded with its identity. -/
public def load? (hashFile : FilePath) : BaseIO (Option Hash) := do
  let some l ← loadedRef.get | Hash.load? hashFile
  let path := hashFile.toString
  -- (the file is read after this, so that a write after it changes the identity recorded)
  let some id ← Lean.PaperLean.fileIdentity path | Hash.load? hashFile
  if let some e := l.entries[path]? then
    if e.identity == id then
      hitsRef.modify (path :: ·)
      return some ⟨e.hash⟩
  let h? ← Hash.load? hashFile
  if let some h := h? then
    let (mt, ct) := changeTimes id
    if mt < l.before && ct < l.before then
      newRef.modify ((path, { identity := id, hash := h.val }) :: ·)
  return h?

/-- Writes the record at the end of the build, of the files that the build read, if it changed. -/
public def finish : BaseIO Unit := do
  let some l ← loadedRef.swap none | return
  let hits ← hitsRef.swap []
  let new ← newRef.swap []
  removeStaleTemps l.file
  let read : Std.HashMap String Entry := hits.foldl (init := {}) fun m p =>
    match l.entries[p]? with
    | some e => m.insert p e
    | none => m
  if new.isEmpty && read.size == l.entries.size then return
  let entries := new.foldl (fun m (p, e) => m.insert p e) read
  let tmp := l.file.addExtension s!"tmp.{← IO.Process.getPID}"
  discard <| (do
    IO.FS.writeBinFile tmp (encode entries)
    IO.FS.rename tmp l.file).toBaseIO

end Lake.PaperLean.HashCache
