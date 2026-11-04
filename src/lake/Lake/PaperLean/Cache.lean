/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Init.System.IO
public import Lean.Data.Json.FromToJson
import Init.Data.Array.QSort.Basic
import Init.Data.Repr
import Init.Data.String.Search
import Init.Data.String.Length
import Init.Data.String.Modify
import Init.System.Platform
import Std.Data.HashSet.Basic
import Lake.Config.Env
import Lake.PaperLean.Env
import Lean.PaperLean.System
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer

/-!
PaperLean's cache of prepared data, shared by the workspaces of a user: per package, entries that
`paperlean prepare` writes once for the package's files and every workspace with the same files uses.
It is `PAPERLEAN_CACHE_DIR`, or `paperlean` in the user's cache directory, with a directory per build of
PaperLean (`buildDir`) that holds
- `pack/<package>-<key>/pack.paperlean`: an olean pack of the package's files, which workspaces read
  through bindings of their own (`Lean.PaperLean.OLeanPack.bind`), keyed by the package's name and the
  paths, sizes and content hashes of its files;
- `native/<package>-<key>/`: its native library with the library's manifest, which knows the modules'
  files by their content hashes, and what `prepare` found (`native.json`), keyed by the key of its
  pack, the `.c` files of its modules, the compiler and the package's configuration, and the keys of
  the libraries that it is linked against;
- `objects/<key>.o`: compiled units of native libraries, keyed by their `.c` files and compiler arguments;
- `slots.json`: the address ranges at which the packs are mapped (`reserveSlot`), disjoint, so that a
  process can map the packs of all of a workspace's packages;
- `users/`: the workspaces that use entries, whose `env.json` keep them from `clean` (`collect`);
- `used/`: when an entry was last used.

An entry is written to a temporary directory and renamed into place holding the lock of its key
(`withKeyLock`), and never changed afterwards. Commands that use entries hold the cache's lock shared
(`withCacheUse`), and `collect` holds it exclusively. A missing entry only makes a workspace's data
unusable, which Lean then reads from disk. Lean's library has a pack of its own
(`Lake.PaperLean.BuildData.toolchainPack`), next to these directories.
-/

open System Lean

namespace Lake.PaperLean.Cache

/-- PaperLean's directory in the user's cache directory, or `PAPERLEAN_CACHE_DIR`. -/
public def root? : BaseIO (Option FilePath) := do
  if let some dir ← IO.getEnv "PAPERLEAN_CACHE_DIR" then
    return some (FilePath.mk dir)
  return (· / "paperlean") <$> (← getSystemCacheHome?)

/-- The name of the directory of this build's entries. -/
public def buildName : String :=
  s!"{Lean.PaperLean.version}+{Lean.PaperLean.build}-{System.Platform.target}"

/-- The directory of this build's entries in the cache `root`. -/
public def buildDir (root : FilePath) : FilePath := root / "prepared" / buildName

/-- `s` with the characters that may not be in a file name replaced. -/
public def fileNamePart (s : String) : String :=
  s.map fun c => if c.isAlphanum || c == '-' || c == '_' || c == '.' then c else '_'

/-- A key: 16 hexadecimal digits of a hash of `parts`. -/
public def key (parts : Array String) : String :=
  let h := parts.foldl (fun h p => mixHash h (hash p)) (hash parts.size)
  let hex := String.ofList (Nat.toDigits 16 h.toNat)
  "".pushn '0' (16 - hex.length) ++ hex

/-- The name of the entry of `pkg` (`Package.baseName`) with `key` in `pack/` or `native/`. -/
public def entryName (pkg key : String) : String := s!"{fileNamePart pkg}-{key}"

/-- Runs `act` holding the lock of the file `lock` (created if missing), waiting for it. -/
public def withFileLock [Monad m] [MonadFinally m] [MonadLiftT IO m] (lock : FilePath) (exclusive : Bool)
    (act : m α) : m α := do
  let h ← liftM (m := IO) do
    if let some parent := lock.parent then IO.FS.createDirAll parent
    let h ← IO.FS.Handle.mk lock .append
    h.lock exclusive
    pure h
  try act finally liftM (m := IO) h.unlock

/-- Runs `act`, which uses the entries of `dir` (`buildDir`), holding the cache's lock shared, so that
`collect` does not delete entries meanwhile. -/
public def withCacheUse [Monad m] [MonadFinally m] [MonadLiftT IO m] (dir : FilePath) (act : m α) : m α :=
  withFileLock (dir / "cache.lock") false act

/-- Runs `act`, which writes the entry `name` (e.g. `pack/<name>`) of `dir` if it is still missing,
holding the entry's lock, so that concurrent commands write it once. -/
public def withKeyLock [Monad m] [MonadFinally m] [MonadLiftT IO m] (dir : FilePath) (name : String)
    (act : m α) : m α :=
  withFileLock (dir / "locks" / s!"{name.replace "/" "-"}.lock") true act

/-- Takes the lock of the entry `name` of `dir`, waiting for it, as `withKeyLock` does, for the caller to
release (`IO.FS.Handle.unlock`): a command that writes several entries takes their locks in the order of
their names. -/
public def lockKey (dir : FilePath) (name : String) : IO IO.FS.Handle := do
  let lock := dir / "locks" / s!"{name.replace "/" "-"}.lock"
  IO.FS.createDirAll (dir / "locks")
  let h ← IO.FS.Handle.mk lock .append
  h.lock (exclusive := true)
  return h

/-- A temporary directory for the entry `entry` of `dir` (e.g. `pack/<name>`), next to where it goes,
named so that `collect` can tell whether its writer still runs. -/
public def tempDir (dir : FilePath) (entry : String) : IO FilePath := do
  let p : FilePath := dir / entry
  return p.withFileName s!".tmp-{← IO.Process.getPID}-{p.fileName.getD ""}"

/-- Moves the finished directory `tmp` to the entry `entry` of `dir`, where nothing is (as its lock is
held). -/
public def publish (dir tmp : FilePath) (entry : String) : IO Unit := do
  IO.FS.rename tmp (dir / entry)

/-- Notes that the entries `entries` of `dir` were used now. -/
public def touch (dir : FilePath) (entries : Array String) : IO Unit := do
  IO.FS.createDirAll (dir / "used")
  for e in entries do
    IO.FS.writeFile (dir / "used" / e.replace "/" "-") ""

/-! ### Address ranges of packs -/

/-- An address range reserved for the pack of an entry. -/
structure Slot where
  base : Nat
  size : Nat
  /-- The entry's directory (`pack/<name>`), or the temporary directory it is written in. -/
  entry : String
  deriving ToJson, FromJson, Inhabited

/-- Where the slots lie: above the addresses that other packs are mapped at (`BuildData`), in steps of
`slotAlign`. -/
def slotsStart : Nat := 0x400000000000
def slotsEnd : Nat := 0x700000000000
def slotAlign : Nat := 0x40000000

def readSlots (dir : FilePath) : IO (Array Slot) := do
  let file := dir / "slots.json"
  unless ← file.pathExists do return #[]
  match Json.parse (← IO.FS.readFile file) >>= fromJson? with
  | .ok slots => return slots
  | .error _ => return #[]

def writeSlots (dir : FilePath) (slots : Array Slot) : IO Unit := do
  let tmp := dir / s!"slots.json.tmp.{← IO.Process.getPID}"
  IO.FS.writeFile tmp ((toJson slots).compress ++ "\n")
  IO.FS.rename tmp (dir / "slots.json")

/-- The process that writes the temporary directory named `name` (`tempDir`), if it is one. -/
def writerOf? (name : String) : Option Nat :=
  (name.dropPrefix? ".tmp-").bind fun rest =>
    (rest.toString.split '-' |>.toStringList).head?.bind String.toNat?

/-- Whether the directory `entry` of a slot of `dir` still exists: a temporary one whose writer ended
does not count. -/
def slotUsed (dir : FilePath) (entry : String) : IO Bool := do
  let p : FilePath := dir / entry
  if let some pid := writerOf? (p.fileName.getD "") then
    unless ← Lean.PaperLean.processAlive pid.toUInt32 do return false
  p.pathExists

/-- Reserves an address range of at least `size` bytes, disjoint from those of the other packs of `dir`,
for the pack that is written in the temporary directory `entry`; its base. -/
public def reserveSlot (dir : FilePath) (entry : String) (size : Nat) : IO USize := do
  let size := (size + slotAlign - 1) / slotAlign * slotAlign
  withFileLock (dir / "slots.lock") true do
    let slots ← (← readSlots dir).filterM (slotUsed dir ·.entry)
    let sorted := slots.qsort (·.base < ·.base)
    let mut base := slotsStart
    for s in sorted do
      if base + size ≤ s.base then break
      base := max base (s.base + s.size)
    if base + size > slotsEnd then
      throw <| IO.userError s!"no address range of {size} bytes is free for a pack in {dir}; \
        `paperlean clean --cache` frees those of unused entries"
    writeSlots dir (slots.push { base, size, entry })
    return base.toUSize

/-- Publishes a finished pack; the caller holds its key lock. Both paths are relative to `dir`, and
`tmp` must have the reservation used to write the pack. The slot's final owner is recorded before the
directory is renamed, holding `slots.lock` throughout: allocators must never see a published pack
whose slot still names the temporary directory that the rename removed. If the process ends before
the rename, the final directory is missing and the slot can safely be reclaimed; afterwards it exists
and keeps the slot. A failed rename restores the pending reservation for the caller to release. -/
public def publishPack (dir : FilePath) (tmp entry : String) (size : Nat) : IO Unit :=
  withFileLock (dir / "slots.lock") true do
    let slots ← readSlots dir
    let reserved := slots.filter (·.entry == tmp)
    let size := (size + slotAlign - 1) / slotAlign * slotAlign
    if reserved.size != 1 || size > reserved[0]!.size then
      throw <| IO.userError s!"the pack {entry} has no matching address range reserved in {dir}"
    writeSlots dir <| slots.map fun s =>
      if s.entry == tmp then { s with entry, size } else s
    try
      publish dir (dir / tmp) entry
    catch e =>
      writeSlots dir slots
      throw e

/-- Changes a reservation's owner and size, or drops it (`none`) when it is given up. Publishing a
pack must use `publishPack`, which also orders the directory rename with respect to allocators. -/
public def settleSlot (dir : FilePath) (tmp : String) (entry : String) (size? : Option Nat) : IO Unit :=
  withFileLock (dir / "slots.lock") true do
    let slots ← readSlots dir
    writeSlots dir <| slots.filterMap fun s =>
      if s.entry != tmp then some s else
      size?.map fun size => { s with entry, size := (size + slotAlign - 1) / slotAlign * slotAlign }

/-! ### Workspaces that use entries -/

/-- Records that the workspace in `wsDir` uses entries of `dir`. -/
public def addUser (dir wsDir : FilePath) : IO Unit := do
  IO.FS.createDirAll (dir / "users")
  let file := dir / "users" / s!"{key #[wsDir.toString]}.json"
  let text := (Json.mkObj [("workspace", wsDir.toString)]).compress ++ "\n"
  if let .ok old ← (IO.FS.readFile file).toBaseIO then
    if old == text then return
  IO.FS.writeFile file text

/-- The path relative to the cache directory of the entry `entry` (e.g. `pack/<name>`) of this build. -/
public def entryPath (entry : String) : String := s!"prepared/{buildName}/{entry}"

/-- The entries of this build that the data in `wsDir` uses, as `env.json` says: `none` if it cannot be
read, so that nothing that it may use is deleted. -/
def usedBy (wsDir : FilePath) : IO (Option (Array String)) := do
  match ← readPreparedData wsDir with
  | none => return some #[]
  | some (.error _) => return none
  | some (.ok d) =>
    if d.mismatch?.isSome then return some #[]
    let paths := (d.deps.map (·.pack) ++ d.libs.map (·.entry)).filter (!·.isEmpty)
    return some <| paths.filterMap fun p => (p.dropPrefix? (entryPath "")).map (·.toString)

/-- What `collect` did: the entries deleted and their size, and those kept. -/
public structure Collected where
  deleted : Nat := 0
  bytes : Nat := 0
  kept : Nat := 0

/-- The size of the files below `p`. -/
partial def sizeOf (p : FilePath) : IO Nat := do
  let md ← p.symlinkMetadata
  if md.type != .dir then return md.byteSize.toNat
  (← p.readDir).foldlM (fun n e => return n + (← sizeOf e.path)) 0

/--
Deletes the entries of `dir` that no registered workspace's `env.json` lists (a workspace that no
longer exists is forgotten), and that were not used in the last `unusedFor` seconds; the temporary
directories of writers that ended; and the objects compiled before that time and more than a week
ago. Holds the cache's lock exclusively.
-/
public def collect (dir : FilePath) (unusedFor : Nat) : IO Collected := do
  unless ← dir.isDir do return {}
  withFileLock (dir / "cache.lock") true do
    let mut used : Std.HashSet String := {}
    if ← (dir / "users").isDir then
      for u in ← (dir / "users").readDir do
        let ws? := (Json.parse (← IO.FS.readFile u.path)).toOption.bind fun j =>
          (j.getObjValAs? String "workspace").toOption
        let some ws := ws? | IO.FS.removeFile u.path; continue
        unless ← (dataDir ws / "env.json").pathExists do
          IO.FS.removeFile u.path
          continue
        match ← usedBy ws with
        | some es => used := used.insertMany es
        | none => used := used.insert "*"
    let now ← Lean.PaperLean.wallSeconds
    let mut out : Collected := {}
    for sub in ["pack", "native"] do
      unless ← (dir / sub).isDir do continue
      for e in ← (dir / sub).readDir do
        let entry := s!"{sub}/{e.fileName}"
        if let some pid := writerOf? e.fileName then
          unless ← Lean.PaperLean.processAlive pid.toUInt32 do
            removePath e.path
          continue
        let last ← lastUse dir entry
        if used.contains "*" || used.contains entry || (unusedFor > 0 && last + unusedFor > now) then
          out := { out with kept := out.kept + 1 }
          continue
        let size ← sizeOf e.path
        removePath e.path
        removePath (dir / "used" / entry.replace "/" "-")
        out := { out with deleted := out.deleted + 1, bytes := out.bytes + size }
    -- (an object is used whenever a library of its unit is built, which may be a while after it was
    -- compiled, so these are kept for a week at least)
    if ← (dir / "objects").isDir then
      for e in ← (dir / "objects").readDir do
        let md ← e.path.metadata
        if md.modified.sec.toNat + max unusedFor (7 * 86400) < now then
          out := { out with bytes := out.bytes + md.byteSize.toNat }
          removePath e.path
    let slots ← readSlots dir
    writeSlots dir (← slots.filterM (slotUsed dir ·.entry))
    return out
where
  /-- When `entry` was last used, in seconds since the epoch (as file times are). -/
  lastUse (dir : FilePath) (entry : String) : IO Nat := do
    match ← (dir / "used" / entry.replace "/" "-").metadata.toBaseIO with
    | .ok md => return md.modified.sec.toNat
    | .error _ => return 0

end Lake.PaperLean.Cache
