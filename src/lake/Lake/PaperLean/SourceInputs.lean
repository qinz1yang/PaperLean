/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import Lake.Build.Job.Monad
import all Lake.PaperLean.SourceInputScope
import Lean.Elab.ParseImportsFast
import Lake.Config.Monad
import Lake.Build.Trace
import Lake.PaperLean.Env
import Lake.PaperLean.Cache
import Lean.PaperLean.OLeanPack
import Init.While
import Std.Data.HashMap.Basic

namespace Lake.PaperLean.SourceInputs

set_option genSizeOf false
open System Lean

/-- Device, inode, size, mtime and ctime of a stable, opened, readable regular file.
The bytes have the same representation as OLeanPack.readVerifiedOwnedBytes expects.
Unsupported systems and final symlinks produce no identity. -/
@[noinline] private def readableIdentity (path : @& String) : BaseIO (Option ByteArray) :=
  Lean.PaperLean.readableSourceIdentity path

private def maxRows := 32768
private def maxNames := 262144
private def maxImports := 65536
private def maxBody := 32 * 1024 * 1024
private def maxSource := 4 * 1024 * 1024

private structure Entry where
  identity : ByteArray
  header : ModuleHeader
  hash : Hash
  deriving Inhabited

private abbrev Table := Std.HashMap String Entry

private def word (bytes : ByteArray) (start n : Nat) : UInt64 := Id.run do
  let mut out : UInt64 := 0
  for j in [0:n] do out := out ||| ((bytes[start+j]!).toUInt64 <<< (8*j).toUInt64)
  return out

private def put (bytes : ByteArray) (n : Nat) (x : UInt64) : ByteArray := Id.run do
  let mut bytes := bytes
  for j in [0:n] do bytes := bytes.push (x >>> (8*j).toUInt64).toUInt8
  return bytes

private def putStr (bytes : ByteArray) (s : String) : ByteArray :=
  put bytes 4 s.utf8ByteSize.toUInt64 ++ s.toUTF8

private abbrev ReadM := StateT Nat Option

private def take (b : ByteArray) (count : Nat) : ReadM ByteArray := do
  let i ← get
  guard <| i + count ≤ b.size
  set (i + count)
  return b.extract i (i + count)

private def readWord (b : ByteArray) (n : Nat) : ReadM UInt64 := do
  let i ← get
  guard <| i + n ≤ b.size
  set (i+n)
  return word b i n

private def readNat (b : ByteArray) : ReadM Nat := return (← readWord b 4).toNat

private def readStr (b : ByteArray) : ReadM String := do
  let some s := String.fromUTF8? (← take b (← readNat b)) | failure
  return s

private def recordPrefix (workspace : String) : ByteArray :=
  putStr s!"PAPERLEAN-source-inputs-1 {Cache.buildName} {Lean.githash}\n".toUTF8 workspace

private def decodeBody (b : ByteArray) : ReadM Table := do
  let n ← readNat b
  guard <| n ≤ maxNames && n ≤ b.size / 8
  let mut names := #[Name.anonymous]
  let mut depths := #[0]
  for _ in [:n] do
    let parent ← readNat b
    guard <| parent < names.size
    let component ← readStr b
    guard <| component.utf8ByteSize ≤ 65535 && !component.contains (Char.ofNat 0) && depths[parent]! < 256
    names := names.push (Name.str names[parent]! component)
    depths := depths.push (depths[parent]! + 1)
  let rows ← readNat b
  guard <| rows ≤ maxRows && rows ≤ b.size / 73
  let mut entries : Table := {}
  for _ in [:rows] do
    let path ← readStr b
    guard <| !path.isEmpty && !path.contains (Char.ofNat 0) && !entries.contains path
    let identity ← take b 56
    guard <| (word identity 16 8).toNat ≤ maxSource &&
      word identity 32 8 < 1000000000 && word identity 48 8 < 1000000000
    let hash := Hash.mk (← readWord b 8)
    let flag ← readWord b 1
    guard <| flag ≤ 1
    let count ← readNat b
    guard <| count ≤ maxImports && (← get) + 5*count ≤ b.size
    let mut imports := #[]
    for _ in [:count] do
      let id ← readNat b
      let f ← readWord b 1
      guard <| 0 < id && id < names.size && f ≤ 7
      imports := imports.push {
        module := names[id]!, importAll := f &&& 1 != 0
        isExported := f &&& 2 != 0, isMeta := f &&& 4 != 0 }
    entries := entries.insert path {identity, hash, header := {isModule := flag == 1, imports}}
  guard <| (← get) == b.size
  return entries

private def decode (workspace : String) (bytes : ByteArray) : Option Table := do
  let head := recordPrefix workspace
  guard <| head.size + 8 ≤ bytes.size && bytes.size ≤ head.size + 8 + maxBody &&
    bytes.extract 0 head.size == head
  let body := bytes.extract (head.size+8) bytes.size
  guard <| body.hash == word bytes head.size 8
  return (← (decodeBody body).run 0).1

private structure NameTable where
  ids : Std.HashMap Name Nat := {}
  data : ByteArray := .empty
  deriving Inhabited

private def intern : Name → NameTable → Nat → Option (Nat × NameTable)
  | .anonymous, t, _ => some (0,t)
  | .num .., _, _ => none
  | n@(.str parent component), t, depth => do
    guard <| depth < 256
    if let some id := t.ids[n]? then return (id,t)
    let (p,t) ← intern parent t (depth+1)
    let id := t.ids.size + 1
    guard <| id ≤ maxNames && component.utf8ByteSize ≤ maxBody
    return (id, {ids := t.ids.insert n id, data := putStr (put t.data 4 p.toUInt64) component})

private def encode (workspace : String) (entries : Array (String × Entry)) : Option ByteArray := do
  let mut names := ({} : NameTable)
  let mut rows := ByteArray.empty
  for (path, e) in entries do
    rows := put (putStr rows path ++ e.identity) 8 e.hash.val
    rows := put (rows.push (if e.header.isModule then 1 else 0)) 4 e.header.imports.size.toUInt64
    for imp in e.header.imports do
      let (id, next) ← intern imp.module names 0
      guard <| id != 0
      names := next
      let flags : UInt8 := (if imp.importAll then 1 else 0) |||
        (if imp.isExported then 2 else 0) ||| (if imp.isMeta then 4 else 0)
      rows := (put rows 4 id.toUInt64).push flags
  let body := put (put .empty 4 names.ids.size.toUInt64 ++ names.data) 4 entries.size.toUInt64 ++ rows
  guard <| body.size ≤ maxBody
  return put (recordPrefix workspace) 8 body.hash ++ body

private def eligibleIdentity (clock : ByteArray) (before : Int) (id : ByteArray) : Bool :=
  id.size == 56 && word id 0 8 == word clock 0 8 && (word id 16 8).toNat ≤ maxSource &&
    (word id 24 8).toInt64.toInt < before && (word id 40 8).toInt64.toInt < before

private def Entry.bytes (e : Entry) : Nat := (word e.identity 16 8).toNat
private def Entry.mtime (e : Entry) : MTime := ⟨(word e.identity 24 8).toInt64.toInt, (word e.identity 32 8).toUInt32⟩

private structure Changes where
  entries : Table := {}
  size : Nat := 8

private structure Session where
  workspace : String
  cacheDir : FilePath
  entryName : String
  file : FilePath
  clock : ByteArray
  before : Int
  entries : Table
  changes : IO.Ref Changes
  hits? : Option (IO.Ref Nat)

private initialize sessions : BuildSessions Session ← BuildSessions.new

private def beginCore (dir : FilePath) (touchRead := true) : IO Session := do
  let some cacheRoot ← Cache.root? | throw <| IO.userError "no user cache"
  let workspace := (← IO.FS.realPath dir).toString
  let cacheDir := Cache.buildDir cacheRoot
  let entryName := Cache.sourceInputEntry workspace
  let base := dir / ".lake"
  IO.FS.createDirAll base
  let path := base / s!"paperlean-sources-clock.tmp.{← IO.Process.getPID}-{← freshGeneration}"
  unless ← writeNewFile path (fun _ => pure ()) do throw <| IO.userError "clock unavailable"
  let clock ← try readableIdentity path.toString finally discard <| (IO.FS.removeFile path).toBaseIO
  let some clock := clock | throw <| IO.userError "unsupported filesystem"
  let before := min (word clock 24 8).toInt64.toInt (word clock 40 8).toInt64.toInt - 2
  let file := cacheDir / entryName
  let max := (recordPrefix workspace).size + 8 + maxBody
  let entries ← Cache.withCacheUse cacheDir do
    let dir := cacheDir / "inputs"
    IO.FS.createDirAll dir
    unless (← dir.symlinkMetadata).type == IO.FS.FileType.dir do throw <| IO.userError "not a cache directory"
    let entries := match ← (Lean.PaperLean.SetupIndex.readRegularPrefix file.toString max.toUSize).toBaseIO with
      | .ok (some (size, b)) => if size.toNat == b.size then (decode workspace b).getD {} else {}
      | _ => {}
    if touchRead && !entries.isEmpty then Cache.touch cacheDir #[entryName]
    pure entries
  let hits? ← if (← IO.getEnv "PAPERLEAN_SOURCE_INPUT_STATS") == some "1" then some <$> IO.mkRef 0 else pure none
  return {workspace, cacheDir, entryName, file, clock, before, entries, changes := ← IO.mkRef {}, hits?}

private def usablePath (path : FilePath) : Bool :=
  path.isAbsolute && !path.toString.contains (Char.ofNat 0)

private def Session.hit? (s : Session) (path : FilePath) (recent? : Option Entry := none) : BaseIO (Option Entry) := do
  unless usablePath path do return none
  let some e := recent? <|> s.entries[path.toString]? | return none
  unless eligibleIdentity s.clock s.before e.identity do return none
  -- The open checks permissions, rejects symlinks/FIFOs and checks the full
  -- descriptor and final path identity. No source contents are read on a hit.
  unless (← readableIdentity path.toString) == some e.identity do return none
  if let some hits := s.hits? then hits.modify (·+1)
  return some e

private structure Captured where
  identity : ByteArray
  contents : String

private def Session.capture? (s : Session) (path : FilePath) : BaseIO (Option Captured) := do
  unless usablePath path do return none
  let some identity ← Lean.PaperLean.OLeanPack.ownedFileIdentity path.toString | return none
  unless eligibleIdentity s.clock s.before identity do return none
  let .ok bytes ← (Lean.PaperLean.OLeanPack.readVerifiedOwnedBytes path.toString identity "").toBaseIO | return none
  let some contents := String.fromUTF8? bytes | return none
  return some {identity, contents}

-- Reserve conservative space for complete records; the encoder interns shared
-- name prefixes and can only produce a smaller representation.
private def nameSize (name : Name) : Option Nat := go name 0 0
where
  go : Name → Nat → Nat → Option Nat
    | .anonymous, _, size => some size
    | .num .., _, _ => none
    | .str p c, depth, size =>
      if depth ≥ 256 || c.utf8ByteSize > 65535 || c.contains (Char.ofNat 0) then none
      else go p (depth+1) (size+8+c.utf8ByteSize)

private def entrySize (path : String) (e : Entry) : Option Nat := do
  guard <| e.header.imports.size ≤ maxImports && e.identity.size == 56
  let mut n := 73 + path.utf8ByteSize
  for imp in e.header.imports do
    guard <| !imp.module.isAnonymous
    n := n + 5 + (← nameSize imp.module)
  return n

private def Session.remember (s : Session) (path : FilePath) (capture : Captured) (hash : Hash)
    (header : ModuleHeader) (mtime : MTime) : BaseIO Unit := do
  let e := {identity := capture.identity, header, hash : Entry}
  unless e.bytes == capture.contents.utf8ByteSize && e.mtime == mtime &&
      (← Lean.PaperLean.OLeanPack.ownedFileIdentity path.toString) == some capture.identity do return
  let some size := entrySize path.toString e | return
  if size > maxBody then return
  s.changes.modify fun c =>
    if c.entries.size ≥ maxRows || c.entries.contains path.toString || c.size+size > maxBody then c
    else {entries := c.entries.insert path.toString e, size := c.size+size}

private def finish (s : Session) : BaseIO Unit := do
  let changes := (← s.changes.get).entries
  if let some hits := s.hits? then
    discard <| (IO.eprintln s!"PaperLean source inputs: hits={← hits.get} new={changes.size}").toBaseIO
  if changes.isEmpty then return
  let add := fun (result : Array (String × Entry) × Nat) (path : String) (entry : Entry) => Id.run do
    let (rows, size) := result
    if rows.size ≥ maxRows then return result
    let some n := entrySize path entry | return result
    if size + n > maxBody then return result
    return (rows.push (path, entry), size+n)
  let chosen := changes.fold add (#[],8)
  let chosen := s.entries.fold (fun acc path e => if changes.contains path then acc else add acc path e) chosen
  let some bytes := encode s.workspace chosen.1 | return
  -- Concurrent runs may replace the whole cache. Every retained row is verified
  -- again on use, and a racing older generation can only cause additional misses.
  discard <| (Cache.withCacheUse s.cacheDir do
    let dir := s.cacheDir / "inputs"
    IO.FS.createDirAll dir
    unless (← dir.symlinkMetadata).type == IO.FS.FileType.dir do return
    publishFile s.file (·.write bytes)
    Cache.touch s.cacheDir #[s.entryName]).toBaseIO

private def current? (ctx : BuildContext) : BaseIO (Option Session) := do
  if let some s ← sessions.find? ctx then return some s
  SourceInputScope.attach ctx do
    let .ok s ← (beginCore ctx.workspace.dir).toBaseIO | return pure ()
    sessions.insert ctx s
    return do
      if let some live ← sessions.take? ctx then finish live
  sessions.find? ctx

/-- Only data needed by Lake's selected builtin input. No API saves a caller's
header, hash, contents, or file identity. -/
public structure Result where
  header : ModuleHeader
  trace : BuildTrace
  bytes : Nat

private def readContents (cache? : Option Session) (path : FilePath) : IO (Option Captured × String) := do
  let capture? ← match cache? with
    | some cache => cache.capture? path
    | none => pure none
  let contents ← match capture? with
    | some cap => pure cap.contents
    | none => IO.FS.readFile path
  return (capture?, contents)

private def original (path : FilePath) : JobM Result := do
  let cache? ← current? (← getBuildContext)
  let (capture?, contents) ← readContents cache? path
  let trace : BuildTrace := {caption := path.toString, mtime := ← getMTime path, hash := .ofText contents}
  setTrace trace
  let header ← Lean.parseImports' contents path.toString
  if let some cache := cache? then
    if let some cap := capture? then cache.remember path cap trace.hash header trace.mtime
  return {header, trace, bytes := contents.utf8ByteSize}

public inductive Read where
  | hit (result : Result)
  | miss (work : JobM Result)

/-- A synchronous result requires an exact descriptor-verified hit. Every other
input keeps its normal async path, stock parser, trace and diagnostics. -/
public def selectRead (ctx : BuildContext) (path : FilePath) : BaseIO Read := do
  if let some cache ← current? ctx then
    if let some e ← cache.hit? path then
      return .hit {
        header := e.header, trace := {caption := path.toString, mtime := e.mtime, hash := e.hash}
        bytes := e.bytes}
  return .miss (original path)

/-- A prepare command may read headers and, following a successful prepare, save only
the records parsed by this reader. No caller supplies contents, headers or identities. -/
public structure HeaderReader where
  private mk ::
  read : FilePath → IO (Option ModuleHeader)
  save : BaseIO Unit

private def prepareHeader (cache? : Option Session) (path : FilePath) : IO (Option ModuleHeader) := do
  unless ← path.pathExists do return none
  if let some cache := cache? then
    let recent := (← cache.changes.get).entries[path.toString]?
    if let some e ← cache.hit? path recent then return some e.header
  -- Preserve prepare's distinction between a source read error and an unparseable header.
  let (capture?, contents) ← readContents cache? path
  let some header ← (some <$> Lean.parseImports' contents path.toString) <|> pure none | return none
  if let some cache := cache? then
    if let some cap := capture? then
      let hash := Hash.ofText contents
      let e : Entry := {identity := cap.identity, header, hash}
      cache.remember path cap hash header e.mtime
  return some header

/-- Prepare shares the same verified regular-file capture and user cache as selected
module inputs. Read-only users don't create a persistent cache or publish observations. -/
public def headerReader (dir : FilePath) (write := false) : IO HeaderReader := do
  let openSession : IO (Option Session) := do
    if (← IO.getEnv "PAPERLEAN_SOURCE_INPUT_CACHE") == some "0" then return none
    unless write do
      let some cacheRoot ← Cache.root? | return none
      let file := Cache.buildDir cacheRoot / Cache.sourceInputEntry (← IO.FS.realPath dir).toString
      let .ok md ← file.symlinkMetadata.toBaseIO | return none
      unless md.type == .file do return none
    return some (← beginCore dir false)
  let session? := (← openSession.toBaseIO).toOption.join
  return ⟨prepareHeader session?, do
    if write then if let some s := session? then finish s⟩

end Lake.PaperLean.SourceInputs
