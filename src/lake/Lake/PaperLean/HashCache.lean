/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lake.Build.Trace
import Init.While
import Init.System.Promise
public import Lake.PaperLean.BuildSessions
import Lake.PaperLean.Env
import Lean.PaperLean.System
import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic

/-!
The `.hash` files that builds under `paperlean` commands read (`Lake.fetchFileHash`): Lake reads those
of every module that is up to date, seven per module, which take most of the time of a build that
compiles little. A build records the contents of those it read with their identities (inode,
size, modification and status change times: `Lean.PaperLean.fileIdentity`) in
`.lake/paperlean-hashes.paperlean`, and later builds take the contents from there instead of reading
a file whose identity is still that recorded, which one `stat` costs. A file is only recorded if it
was last changed well before the build started (`margin`, by the time of a file it writes then): any
later write changes its identity, even where file systems keep coarse times, and the status change
time cannot be set. The record holds what the last build read. What it held that a build did not read,
as of another target, goes to `.lake/paperlean-hashes-kept.paperlean`, which a build reads only for a
file that the record does not have (and takes it back into the record if it reads it); there an entry
that no build read in `maxAge` changes of that file goes. A record that is missing, damaged, or of
another build is ignored, and so is the entry of a file that changed since; `PAPERLEAN_HASH_CACHE=0`
turns them off.
-/

open System Lean

namespace Lake.PaperLean.HashCache

/-- A `.hash` file as recorded: its identity and the hash it holds; in the kept record, also the
generation of that record (how often it was written) when it was put there. -/
structure Entry where
  identity : ByteArray
  hash : UInt64
  gen : UInt32 := 0

/-- A record as read: its generation and its entries. -/
abbrev Record := UInt32 × Std.HashMap String Entry

/-- The records of the build. -/
structure Loaded where
  file : FilePath
  entries : Std.HashMap String Entry
  /-- Files last changed before this time (s since the epoch) are recorded. -/
  before : Int
  keptFile : FilePath
  /-- Resolved by the first file that `entries` does not have: then `kept` reads the kept record. -/
  wantKept : IO.Promise Unit
  kept : Task Record

private structure Session where
  loaded : Loaded
  hits : IO.Ref (List String)
  keptHits : IO.Ref (List String)
  newEntries : IO.Ref (List (String × Entry))
  gone : IO.Ref (List String)

private initialize runs : BuildSessions (Option Session) ← BuildSessions.new
private initialize standalone : IO.Ref (Option Session) ← IO.mkRef none

/-- The record of a workspace that `prefetch` reads ahead of its build. -/
private initialize prefetchRef : IO.Ref (Option (FilePath × Task Record)) ← IO.mkRef none

/-- How long before the start of the build a file must have been last changed to be recorded (s). -/
private def margin : Int := 2

/-- The number of times the kept record is written before an entry that no build read since it was
put there goes. -/
private def maxAge : UInt32 := 32

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

/-- The header of a record of kind `kind`, as that of PaperLean's side files
(`src/paperlean/side_file.h`): magic, kind, the version and build of PaperLean and Lean's commit that
wrote it, and its size, followed by the checksum of the entries. -/
private def headerOf (kind : String) : ByteArray :=
  padded "PAPERLEAN" 16 ++ padded kind 16 ++
    padded s!"{Lean.PaperLean.version}+{Lean.PaperLean.build}" 64 ++ padded Lean.githash 40 |>
    le 4 (16 + 16 + 64 + 40 + 4 + 4 + 8) |> le 4 0

/-- The kinds of the record and the kept record. -/
private def recordKind : String := "build-hashes"
private def keptKind : String := "kept-hashes"

/-- The entries of a record of kind `kind`, if this build wrote it and it is whole: after the header,
each a path's length (2 bytes) and bytes, its identity and its hash (8 bytes), little-endian. In the
kept record (`gens`), the record's generation (4 bytes) comes first, and each entry ends with its own. -/
private def decode (kind : String) (gens : Bool) (b : ByteArray) : Option Record := Id.run do
  let h := headerOf kind
  if b.size < h.size + 8 || b.extract 0 h.size != h then return none
  let body := b.extract (h.size + 8) b.size
  if rd b h.size 8 != body.hash then return none
  let tail := if gens then 4 else 0
  if body.size < tail then return none
  let gen := (rd body 0 tail).toUInt32
  let mut i := tail
  let mut out : Std.HashMap String Entry := {}
  while i < body.size do
    if i + 2 > body.size then return none
    let n := (rd body i 2).toNat
    let j := i + 2 + n
    if j + identitySize + 8 + tail > body.size then return none
    let some path := String.fromUTF8? (body.extract (i + 2) j) | return none
    out := out.insert path
      { identity := body.extract j (j + identitySize), hash := rd body (j + identitySize) 8
        gen := (rd body (j + identitySize + 8) tail).toUInt32 }
    i := j + identitySize + 8 + tail
  return some (gen, out)

private def encode (kind : String) (gens : Bool) (gen : UInt32) (entries : Std.HashMap String Entry) :
    ByteArray :=
  let tail := if gens then 4 else 0
  let body := entries.fold (init := le tail gen.toUInt64 .empty) fun out path e =>
    let p := path.toUTF8
    if p.size ≥ 65536 || e.identity.size != identitySize then out else
    le tail e.gen.toUInt64 <| le 8 e.hash (le 2 p.size.toUInt64 out ++ p ++ e.identity)
  le 8 body.hash (headerOf kind) ++ body

/-- The record of kind `kind` in `file`; empty if there is none or it cannot be used. -/
private def readRecord (kind : String) (gens : Bool) (file : FilePath) : BaseIO Record := do
  if ← isSpecialFile file then return (0, {})
  match ← (IO.FS.readBinFile file).toBaseIO with
  | .ok b => return (decode kind gens b).getD (0, {})
  | .error _ => return (0, {})

/-- Makes `bytes` the contents of `file`: written to a temporary file and renamed into place. -/
private def install (file : FilePath) (bytes : ByteArray) : BaseIO Unit :=
  discard <| (publishFile file (·.write bytes)).toBaseIO

/-- The modification and status change times (s) of an identity. -/
private def changeTimes (id : ByteArray) : Int × Int :=
  ((rd id 24 8).toInt64.toInt, (rd id 40 8).toInt64.toInt)

/-- The record of the workspace in `wsDir`. -/
public def recordFile (wsDir : FilePath) : FilePath := wsDir / ".lake" / "paperlean-hashes.paperlean"

/-- The kept record of the workspace in `wsDir`. -/
public def keptFile (wsDir : FilePath) : FilePath :=
  wsDir / ".lake" / "paperlean-hashes-kept.paperlean"

/-- Starts reading the record of the workspace in `wsDir` for a build under a `paperlean` command
that is about to start (`start` takes it), while Lake does something else, such as loading the
workspace. -/
public def prefetch (wsDir : FilePath) : BaseIO Unit := do
  if (← IO.getEnv "PAPERLEAN_HASH_CACHE") == some "0" then return
  let file := recordFile wsDir
  let t ← BaseIO.asTask (prio := .dedicated) (readRecord recordKind false file)
  prefetchRef.set (some (file, t))

/-- Starts using the records of the workspace in `wsDir`, at the start of a build under a `paperlean`
command (`accelerated`). -/
private def newSession (wsDir : FilePath) (enabled : Bool) : BaseIO (Option Session) := do
  unless enabled && (← accelerated) do return none
  if (← IO.getEnv "PAPERLEAN_HASH_CACHE") == some "0" then return none
  let file := recordFile wsDir
  let prefetched? ← prefetchRef.modifyGet fun hint =>
    if hint.any (·.1 == file) then (hint.map (·.2), none) else (none, hint)
  let keptFile := keptFile wsDir
  let r ← (do
    IO.FS.createDirAll (wsDir / ".lake")
    -- the file system's time now
    let clock := wsDir / ".lake" / "paperlean-clock.paperlean"
    if (← isSpecialFile clock) || (← isSpecialFile file) then return none
    IO.FS.writeFile clock ""
    let some id ← Lean.PaperLean.fileIdentity clock.toString | return none
    let (mt, ct) := changeTimes id
    let (_, entries) ← match prefetched? with
      | some t => IO.wait t
      | none => readRecord recordKind false file
    let wantKept : IO.Promise Unit ← IO.Promise.new
    let kept ← BaseIO.mapTask (t := wantKept.result?) (prio := .dedicated) fun
      | some () => readRecord keptKind true keptFile
      | none => pure (0, {})
    return some { file, entries, before := min mt ct - margin, keptFile, wantKept, kept : Loaded }).toBaseIO
  let .ok (some loaded) := r | return none
  return some ⟨loaded, ← IO.mkRef [], ← IO.mkRef [], ← IO.mkRef [], ← IO.mkRef []⟩

public def startFor (ctx : BuildContext) (wsDir : FilePath) (enabled : Bool) : BaseIO Unit := do
  runs.insert ctx (← newSession wsDir enabled)

public def start (wsDir : FilePath) : BaseIO Unit := do
  standalone.set (← newSession wsDir true)

/-- The hash in the `.hash` file `hashFile`, as `Hash.load?` reads it, without reading the file if
it is recorded with its identity. -/
private def loadIn (session? : Option Session) (hashFile : FilePath) : BaseIO (Option Hash) := do
  let some s := session? | Hash.load? hashFile
  let l := s.loaded
  let path := hashFile.toString
  -- (the file is read after this, so that a write after it changes the identity recorded)
  let some id ← Lean.PaperLean.fileIdentity path | Hash.load? hashFile
  match l.entries[path]? with
  | some e =>
    if e.identity == id then
      s.hits.modify (path :: ·)
      return some ⟨e.hash⟩
    s.gone.modify (path :: ·)
  | none =>
    l.wantKept.resolve ()
    if let some e := (← IO.wait l.kept).2[path]? then
      if e.identity == id then
        s.keptHits.modify (path :: ·)
        return some ⟨e.hash⟩
      s.gone.modify (path :: ·)
  let h? ← Hash.load? hashFile
  if let some h := h? then
    let (mt, ct) := changeTimes id
    if mt < l.before && ct < l.before then
      s.newEntries.modify ((path, { identity := id, hash := h.val }) :: ·)
  return h?

public def loadFor? (ctx : BuildContext) (hashFile : FilePath) : BaseIO (Option Hash) := do
  loadIn (← runs.find? ctx).join hashFile

public def load? (hashFile : FilePath) : BaseIO (Option Hash) := do
  loadIn (← runs.singleOr? (some (← standalone.get))).join hashFile

/-- Writes the records at the end of the build, if they changed: the record of the files that the
build read, and the kept record of those that the record had and the build did not read, with what it
kept before, less what the build read of it, what changed and what is too old. -/
private def finishSession (s : Session) : BaseIO Unit := do
  let l := s.loaded
  let hits ← s.hits.swap []
  let keptHits ← s.keptHits.swap []
  let new ← s.newEntries.swap []
  let gone ← s.gone.swap []
  removeStaleTemps l.file
  if hits.isEmpty && keptHits.isEmpty && new.isEmpty && gone.isEmpty then return
  -- (a file that is read twice counts twice: then the record may keep an entry that was not read)
  if new.isEmpty && keptHits.isEmpty && gone.isEmpty && hits.length ≥ l.entries.size then return
  let goneSet : Std.HashSet String := gone.foldl (·.insert ·) {}
  let read : Std.HashMap String Entry := hits.foldl (init := {}) fun m p =>
    match l.entries[p]? with
    | some e => m.insert p e
    | none => m
  let unread := l.entries.fold (init := #[]) fun out p e =>
    if read.contains p || goneSet.contains p then out else out.push (p, e)
  -- (read if the build looked up a file there, or if it gets the unread entries)
  let kept? ← if unread.isEmpty && !(← IO.hasFinished l.kept) then pure none else do
    l.wantKept.resolve ()
    pure (some (← IO.wait l.kept))
  let mut entries := read
  if let some (_, k) := kept? then
    entries := keptHits.foldl (init := entries) fun m p =>
      match k[p]? with
      | some e => m.insert p { e with gen := 0 }
      | none => m
  entries := new.foldl (fun m (p, e) => m.insert p e) entries
  install l.file (encode recordKind false 0 entries)
  let some (gen, k) := kept? | return
  if unread.isEmpty && keptHits.isEmpty && !gone.any k.contains && !new.any (k.contains ·.1) then
    return
  removeStaleTemps l.keptFile
  let gen := gen + 1
  let k := k.filter fun p e => !entries.contains p && !goneSet.contains p && gen - e.gen ≤ maxAge
  let k := unread.foldl (init := k) fun k (p, e) => k.insert p { e with gen }
  install l.keptFile (encode keptKind true gen k)

public def finishFor (ctx : BuildContext) : BaseIO Unit := do
  if let some s := (← runs.take? ctx).join then finishSession s

public def finish : BaseIO Unit := do
  if let some s ← standalone.swap none then finishSession s

end Lake.PaperLean.HashCache
