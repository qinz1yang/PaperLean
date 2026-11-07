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
import Lean.Setup
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
- `inputs/`: cached source input facts for unchanged regular files;
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

/-- Create a cache root. Automatically selected per-user caches are private, including before
writing temporary files; an explicit `PAPERLEAN_CACHE_DIR` keeps the caller's sharing policy. -/
public def ensureRoot (root : FilePath) : IO Unit := do
  if (← IO.getEnv "PAPERLEAN_CACHE_DIR").isNone then
    if let some systemCache ← getSystemCacheHome? then
      let defaultRoot := systemCache / "paperlean"
      let isDefault ← if root == defaultRoot then pure true else do
        let .ok actual ← (IO.FS.realPath root).toBaseIO | pure false
        let .ok configured ← (IO.FS.realPath defaultRoot).toBaseIO | pure false
        pure (actual == configured)
      if isDefault then
        try discard <| systemCache.symlinkMetadata catch
          | .noFileOrDirectory .. =>
            if let some parent := systemCache.parent then IO.FS.createDirAll parent
            Lean.PaperLean.privateCacheRoot systemCache.toString
          | e => throw e
        -- Protect the configured alias as well as the actual argument: if the alias
        -- changes after recognition, the caller still writes through its protected root.
        Lean.PaperLean.privateCacheRoot defaultRoot.toString
        if root != defaultRoot then Lean.PaperLean.privateCacheRoot root.toString
        return
  IO.FS.createDirAll root

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

/-- Per-workspace source facts stored alongside this compiler's prepared data. -/
public def sourceInputEntry (workspace : String) : String :=
  "inputs/" ++ key #[workspace] ++ ".paperlean"

/-- The name of the entry of `pkg` (`Package.baseName`) with `key` in `pack/` or `native/`. -/
public def entryName (pkg key : String) : String := s!"{fileNamePart pkg}-{key}"

/-- Inspect the entry itself. A missing entry is distinct from an unreadable one. -/
private def kind? (path : FilePath) : IO (Option IO.FS.FileType) := do
  try return some (← path.symlinkMetadata).type catch
    | .noFileOrDirectory .. => return none
    | e => throw e

/-- Structural directories below the configured root must be real directories.
Creating one component at a time also checks the winner of a concurrent mkdir. -/
private def directory (path : FilePath) (create := false) : IO Bool := do
  if let some kind ← kind? path then return kind == .dir
  unless create do return false
  try IO.FS.createDir path catch
    | .alreadyExists .. => pure ()
    | e => throw e
  return (← kind? path) == some .dir

private def buildDirectory (dir : FilePath) (create := false) : IO Bool := do
  if let some parent := dir.parent then
    if parent.fileName == some "prepared" then
      -- The parent of "prepared" is the configured cache root. It may be a symlink.
      if create then
        if let some root := parent.parent then ensureRoot root
      unless ← directory parent create do return false
    else if create then IO.FS.createDirAll parent
  directory dir create

private def ensureDirectory (dir : FilePath) : IO Unit := do
  unless ← buildDirectory dir true do throw <| IO.userError s!"not a real cache directory: {dir}"

private def ensureChild (dir : FilePath) (name : String) : IO Unit := do
  ensureDirectory dir
  unless ← directory (dir / name) true do
    throw <| IO.userError s!"not a real cache directory: {dir / name}"

/-- Cache metadata must be a complete regular file; a link or FIFO is never opened.
Platforms without the descriptor reader use the same file-type check. -/
private def readText? (file : FilePath) : IO (Option String) := do
  let some kind ← kind? file | return none
  unless kind == .file do throw <| IO.userError s!"not a regular cache file: {file}"
  if let some (n, bytes) ← Lean.PaperLean.SetupIndex.readRegularPrefix file.toString (USize.size - 1).toUSize then
    unless n.toNat == bytes.size do throw <| IO.userError s!"incomplete cache file: {file}"
    let some text := String.fromUTF8? bytes | throw <| IO.userError s!"invalid UTF-8 in {file}"
    return some text
  return some (← IO.FS.readFile file)

private def openLock (lock : FilePath) : IO IO.FS.Handle := do
  if let some parent := lock.parent then
    if parent.fileName == some "locks" then
      if let some dir := parent.parent then ensureChild dir "locks"
    else ensureDirectory parent
  if (← kind? lock).isNone then
    try return ← IO.FS.Handle.mk lock .writeNew catch
      | .alreadyExists .. => pure ()
      | e => throw e
  unless (← kind? lock) == some .file do throw <| IO.userError s!"not a regular lock file: {lock}"
  IO.FS.Handle.mk lock .append

/-- Runs `act` holding the lock of the file `lock` (created if missing), waiting for it. -/
public def withFileLock [Monad m] [MonadFinally m] [MonadLiftT IO m] (lock : FilePath) (exclusive : Bool)
    (act : m α) : m α := do
  let h ← liftM (m := IO) do
    let h ← openLock lock
    h.lock exclusive
    pure h
  try act finally liftM (m := IO) h.unlock

/-- Runs `act`, which uses the entries of `dir` (`buildDir`), holding the cache's lock shared, so that
`collect` does not delete entries meanwhile. -/
public def withCacheUse [Monad m] [MonadFinally m] [MonadLiftT IO m] (dir : FilePath) (act : m α) : m α :=
  withFileLock (dir / "cache.lock") false do
    liftM (m := IO) do
      for sub in ["pack", "native", "objects", "inputs", "users", "used", "locks"] do
        if let some k ← kind? (dir / sub) then
          unless k == .dir do throw <| IO.userError s!"not a real cache directory: {dir / sub}"
    act

private def markerName? (entry : String) : Option String := do
  let name := entry.replace "/" "-"
  guard <| !name.isEmpty && name != "." && name != ".." && !name.contains '\\' &&
    !name.contains (Char.ofNat 0) && !(FilePath.mk name).isAbsolute && (FilePath.mk name).fileName == some name
  return name

private def keyLockFile (dir : FilePath) (name : String) : IO FilePath := do
  let some part := markerName? name | throw <| IO.userError s!"invalid cache lock name: {name}"
  return dir / "locks" / s!"{part}.lock"

/-- Runs `act`, which writes the entry `name` (e.g. `pack/<name>`) of `dir` if it is still missing,
holding the entry's lock, so that concurrent commands write it once. -/
public def withKeyLock [Monad m] [MonadFinally m] [MonadLiftT IO m] (dir : FilePath) (name : String)
    (act : m α) : m α := do
  withFileLock (← liftM (m := IO) (keyLockFile dir name)) true act

/-- Takes the lock of the entry `name` of `dir`, waiting for it, as `withKeyLock` does, for the caller to
release (`IO.FS.Handle.unlock`): a command that writes several entries takes their locks in the order of
their names. -/
public def takeKeyLock (dir : FilePath) (name : String) (exclusive : Bool) : IO IO.FS.Handle := do
  let lock ← keyLockFile dir name
  let h ← openLock lock
  h.lock (exclusive := exclusive)
  return h

/-- Take an exclusive entry lock. -/
public def lockKey (dir : FilePath) (name : String) : IO IO.FS.Handle :=
  takeKeyLock dir name true

/-- A temporary directory for the entry `entry` of `dir` (e.g. `pack/<name>`), next to where it goes,
named so that `collect` can tell whether its writer still runs. -/
public def tempDir (dir : FilePath) (entry : String) : IO FilePath := do
  let p : FilePath := dir / entry
  return p.withFileName s!".tmp-{← IO.Process.getPID}-{p.fileName.getD ""}"

/-- Moves the finished directory `tmp` to the entry `entry` of `dir`, where nothing is (as its lock is
held). -/
public def publish (dir tmp : FilePath) (entry : String) : IO Unit := do
  IO.FS.rename tmp (dir / entry)

/-- Notes that the entries were used now. Replace the marker itself; truncating an
existing inode would also truncate any other name linked to it. -/
public def touch (dir : FilePath) (entries : Array String) : IO Unit := do
  ensureChild dir "used"
  for e in entries do
    let some name := markerName? e | throw <| IO.userError s!"invalid cache marker name: {e}"
    PaperLean.publishFile (dir / "used" / name) (·.putStr "")

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
  let some text ← readText? file | return #[]
  match Json.parse text >>= fromJson? with
  | .ok slots => return slots
  | .error _ => return #[]

def writeSlots (dir : FilePath) (slots : Array Slot) : IO Unit := do
  PaperLean.publishFile (dir / "slots.json") (·.putStr ((toJson slots).compress ++ "\n"))

/-- The process that writes the temporary directory named `name` (`tempDir`), if it is one. -/
def writerOf? (name : String) : Option Nat :=
  (name.dropPrefix? ".tmp-").bind fun rest =>
    (rest.toString.split '-' |>.toStringList).head?.bind String.toNat?

/-- Whether the directory `entry` of a slot of `dir` still exists: a temporary one whose writer ended
does not count. -/
def slotUsed (dir : FilePath) (entry : String) : IO Bool := do
  unless isCachePath entry do return false
  let [sub, name] := (entry.split '/').toStringList | return false
  unless sub == "pack" do return false
  unless ← directory (dir / sub) do return false
  let p := dir / sub / name
  if let some pid := writerOf? name then
    unless ← Lean.PaperLean.processAlive pid.toUInt32 do return false
  return (← kind? p).any fun k => k == .dir || k == .file

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
  ensureChild dir "users"
  let file := dir / "users" / s!"{key #[wsDir.toString]}.json"
  let text := (Json.mkObj [("workspace", wsDir.toString)]).compress ++ "\n"
  if let .ok (some old) ← (readText? file).toBaseIO then
    if old == text then return
  PaperLean.publishFile file (·.putStr text)

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
    let entries := paths.filterMap fun p => (p.dropPrefix? (entryPath "")).map (·.toString)
    let .ok ws ← (IO.FS.realPath wsDir).toBaseIO | return none
    return some <| entries.push (sourceInputEntry ws.toString)

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
  unless ← buildDirectory dir do return {}
  withFileLock (dir / "cache.lock") true do
    let mut used : Std.HashSet String := {}
    let users := dir / "users"
    if let some k ← kind? users then
      -- If the registry cannot be read safely, a live workspace may need any entry.
      if k != .dir then used := used.insert "*"
      else
        for u in ← users.readDir do
          let .ok (some text) ← (readText? u.path).toBaseIO | used := used.insert "*"; continue
          let ws? := (Json.parse text).toOption.bind fun j =>
            (j.getObjValAs? String "workspace").toOption
          let some ws := ws? | IO.FS.removeFile u.path; continue
          unless ← (dataDir ws / "env.json").pathExists do
            IO.FS.removeFile u.path
            continue
          match ← usedBy ws with
          | some es => used := used.insertMany es
          | none => used := used.insert "*"
    let markers ← kind? (dir / "used")
    let now ← Lean.PaperLean.wallSeconds
    let mut out : Collected := {}
    for sub in ["pack", "native", "inputs"] do
      unless ← directory (dir / sub) do continue
      for e in ← (dir / sub).readDir do
        let entry := s!"{sub}/{e.fileName}"
        if let some pid := writerOf? e.fileName then
          unless ← Lean.PaperLean.processAlive pid.toUInt32 do
            removePath e.path
          continue
        let marker := (markerName? entry).map (dir / "used" / ·)
        let last ← if markers == some .dir then
          match marker with
          | some path => pure (((← path.symlinkMetadata.toBaseIO).toOption.map (·.modified.sec.toNat)).getD 0)
          | none => pure now
        else pure (if markers.isSome then now else 0)
        if used.contains "*" || used.contains entry || (unusedFor > 0 && last + unusedFor > now) then
          out := { out with kept := out.kept + 1 }
          continue
        let size ← sizeOf e.path
        removePath e.path
        if markers == some .dir then
          if let some path := marker then removePath path
        out := { out with deleted := out.deleted + 1, bytes := out.bytes + size }
    -- (an object is used whenever a library of its unit is built, which may be a while after it was
    -- compiled, so these are kept for a week at least)
    if ← directory (dir / "objects") then
      for e in ← (dir / "objects").readDir do
        let md ← e.path.symlinkMetadata
        if md.modified.sec.toNat + max unusedFor (7 * 86400) < now then
          out := { out with bytes := out.bytes + md.byteSize.toNat }
          removePath e.path
    if (← kind? (dir / "slots.json")).all (· == .file) then
      let slots ← readSlots dir
      writeSlots dir (← slots.filterM (slotUsed dir ·.entry))
    return out

end Lake.PaperLean.Cache
