/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mac Malone
-/
module

prelude
public import Lean.Data.Json.Parser
public import Lean.Util.LeanOptions
import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic

set_option doc.verso true

public section

/-!
# Module Setup Information

Data types used by Lean module headers and the `--setup` CLI.
-/

namespace Lean

/-- Abstract structure of an {lit}`import` statement. -/
structure Import where
  module     : Name
  /-- `import all`; whether to import and expose all data saved by the module. -/
  importAll  : Bool := false
  /-- Whether to activate this import when the current module itself is imported. -/
  isExported : Bool := true
  /-- Whether to import IR for all definitions (transitively) reachable. -/
  isMeta     : Bool := false
  deriving Repr, Inhabited, ToJson, FromJson,
    BEq, Hashable -- needed by Lake (in `Lake.Load.Elab.Lean`)

-- TODO: move further up into `Init` by using simpler representation for `imports`
@[extern "lean_idbg_client_loop"]
opaque Idbg.idbgClientLoop {α : Type} [Nonempty α]
  (siteId : String) (imports : Array Import) (apply : α → String) : IO Unit

instance : Coe Name Import := ⟨({module := ·})⟩

instance : ToString Import := ⟨fun imp =>
  s!"{if imp.isExported then "public " else ""}{if imp.isMeta then "meta " else ""}import \
    {if imp.importAll then "all " else ""}{imp.module}"⟩

/-- Phases for which some IR is available for execution. -/
inductive IRPhases where
  /-- Available for execution in the final native code. -/
  | runtime
  /-- Available for execution during elaboration. -/
  | comptime
  /-- Available during run time and compile time. -/
  | all
deriving Inhabited, BEq, Repr

/-- Abstract structure of a module's header. -/
structure ModuleHeader where
  /-- The module's direct imports (i.e., those listed in the header). -/
  imports  : Array Import
  /-- Whether the module is participating in the module system. -/
  isModule : Bool
  deriving Repr, Inhabited, ToJson, FromJson

/--
Module data files used for an {lit}`import` statement.
This structure is designed for efficient JSON serialization.
-/
structure ImportArtifacts where
  ofArrays ::
    /--
    Two nested arrays of variable size: {lit}`#[#[olean, oleanServer?, oleanPrivate?], #[irSig, ir?]]`
    -/
    toArrays : Array (Array System.FilePath)
  deriving Repr, Inhabited

instance : ToJson ImportArtifacts := ⟨(toJson ·.toArrays)⟩
instance : FromJson ImportArtifacts := ⟨(.ofArrays <$> fromJson? ·)⟩

def ImportArtifacts.olean? (arts : ImportArtifacts) : Option System.FilePath :=
  arts.toArrays[0]?.bind (·[0]?)

def ImportArtifacts.oleanServer? (arts : ImportArtifacts) : Option System.FilePath :=
  arts.toArrays[0]?.bind (·[1]?)

def ImportArtifacts.oleanPrivate? (arts : ImportArtifacts) : Option System.FilePath :=
  arts.toArrays[0]?.bind (·[2]?)

def ImportArtifacts.irSig? (arts : ImportArtifacts) : Option System.FilePath :=
  arts.toArrays[1]?.bind (·[0]?)

def ImportArtifacts.ir? (arts : ImportArtifacts) : Option System.FilePath :=
  arts.toArrays[1]?.bind (·[1]?)

def ImportArtifacts.oleanParts (inServer : Bool) (arts : ImportArtifacts) : Array System.FilePath := Id.run do
  let mut fnames := #[]
  if let some mFile := arts.olean? then
    fnames := fnames.push mFile
    if let some sFile := arts.oleanServer? then
      -- For uniformity, Lake always provides us with .olean.server, so load it only when we are in
      -- server mode or we need it to load further files.
      if inServer || arts.oleanPrivate?.isSome then
        fnames := fnames.push sFile
      if let some pFile := arts.oleanPrivate? then
        fnames := fnames.push pFile
  return fnames

def ImportArtifacts.irParts (arts : ImportArtifacts) : Array System.FilePath :=
  arts.toArrays[1]?.getD #[]

/-- Files containing data for a single module. -/
structure ModuleArtifacts where
  lean? : Option System.FilePath := none
  olean? : Option System.FilePath := none
  oleanServer? : Option System.FilePath := none
  oleanPrivate? : Option System.FilePath := none
  ilean? : Option System.FilePath := none
  irSig? : Option System.FilePath := none
  ir? : Option System.FilePath := none
  c? : Option System.FilePath := none
  bc? : Option System.FilePath := none
  deriving Repr, Inhabited, ToJson, FromJson

def ModuleArtifacts.oleanParts (arts : ModuleArtifacts) : Array System.FilePath := Id.run do
  let mut fnames := #[]
  if let some mFile := arts.olean? then
    fnames := fnames.push mFile
    if let some sFile := arts.oleanServer? then
      fnames := fnames.push sFile
      if let some pFile := arts.oleanPrivate? then
        fnames := fnames.push pFile
  return fnames

def ModuleArtifacts.irParts (arts : ModuleArtifacts) : Array System.FilePath := Id.run do
  let mut fnames := #[]
  if let some irSigFile := arts.irSig? then
    fnames := fnames.push irSigFile
    if let some irFile := arts.ir? then
      fnames := fnames.push irFile
  return fnames

/-- A Lean plugin. Plugins are shared libraries with an initialization function. -/
structure Plugin where
  /-- The path to the plugin's shared library. -/
  path : System.FilePath
  /--
  The name of the plugin initialization function symbol.
  If {lean}`none`, the symbol is derived from the file name of the shared library.
  -/
  initFn? : Option String
  deriving Repr, ToJson

namespace Plugin

/--
Constructs a plugin from just a shared library's {lean}`path`,
inferring the name of the initialization function from the library's name.
-/
def ofFilePath (path : System.FilePath) : Plugin :=
  {path, initFn? := none}

instance : Coe System.FilePath Plugin := ⟨ofFilePath⟩

protected def fromJson? (data : Json) : Except String Plugin := do
  match data with
  | .str path =>
    return .ofFilePath path
  | data@(.obj _) =>
    let path ← data.getObjValAs? _ "path"
    let initFn? ← data.getObjValAs? _ "initFn"
    return {path, initFn?}
  | _ =>
    throw "expected string or object"

instance : FromJson Plugin := ⟨Plugin.fromJson?⟩

end Plugin

/--
The type of module package identifiers.

This is a {name}`String` that is used to disambiguate native symbol prefixes between
different packages (and different versions of the same package).
-/
abbrev PkgId := String

/-- A module's setup information as described by a JSON file. -/
structure ModuleSetup where
  /-- The name of the module. -/
  name : Name
  /-- The package to which the module belongs (if any). -/
  package? : Option PkgId := none
  /--
  Whether the module, by default, participates in the module system.
  Even if {lean}`false`, a module can still choose to participate by using
  {lit}`module` in its header.
  -/
  isModule : Bool := false
  /--
  The module's direct imports.
  If {lean}`none`, uses the imports from the module header.
  -/
  imports? : Option (Array Import) := none
  /-- Pre-resolved artifacts of transitively imported modules. -/
  importArts : NameMap ImportArtifacts := {}
  /-- Dynamic libraries to load with the module. -/
  dynlibs : Array System.FilePath := #[]
  /-- Plugins to initialize with the module. -/
  plugins : Array Plugin := #[]
  /-- Additional options for the module. -/
  options : LeanOptions := {}
  deriving Repr, Inhabited, ToJson, FromJson

/-!
{lit}`paperlean` commands: the setup files of the modules that a build compiles. PaperLean's code comes
after the upstream declarations above, whose specializations it reuses, and the instances above are
what `deriving` gives, so that the compiled code of this file up to here is official Lean's.

Lake lists the artifacts of every transitively imported module, so these maps can have tens of
thousands of entries. An entry whose files are a prefix of the usual parts at their default location
below a package root ({lit}`modToFilePath root mod ext`) is therefore encoded as
{lit}`[root, numOLeanParts]` or {lit}`[root, numOLeanParts, numIRParts]`, where {lit}`root` indexes
the array of roots stored under the key {lit}`""` (which cannot name a module). All other entries
keep their full paths.
-/

namespace PaperLean

private def oleanPartExts : Array String := #["olean", "olean.server", "olean.private"]
private def irPartExts : Array String := #["ir.sig", "ir"]

private def hasOnlyStrComponents : Name → Bool
  | .anonymous => true
  | .str p _ => hasOnlyStrComponents p
  | .num .. => false

/-- {lit}`modToFilePath root mod ""`: this module lies below {lit}`Lean.Util.Path`. -/
private def modStem (root : System.FilePath) : Name → System.FilePath
  | .str p h => modStem root p / h
  | _ => root

private def partsAt (root : System.FilePath) (mod : Name) (exts : Array String) (n : Nat) :
    Array System.FilePath :=
  let stem := (modStem root mod).toString
  (exts.extract 0 n).map fun ext => ⟨stem ++ "." ++ ext⟩

/--
If the files of {name}`arts` are at their default location for {name}`mod`, returns their root and
the number of olean parts and, if there is a second array, of IR parts.
-/
private def defaultLayout? (mod : Name) (arts : ImportArtifacts) :
    Option (String × Nat × Option Nat) := do
  guard (!mod.isAnonymous && hasOnlyStrComponents mod && arts.toArrays.size ≤ 2)
  let olean ← arts.olean?
  let root ← (List.range mod.getNumParts).foldlM (init := olean) fun p _ => p.parent
  let oleans := arts.toArrays[0]!
  let irs? := arts.toArrays[1]?
  guard (oleans.size ≤ oleanPartExts.size && oleans == partsAt root mod oleanPartExts oleans.size)
  if let some irs := irs? then
    guard (irs.size ≤ irPartExts.size && irs == partsAt root mod irPartExts irs.size)
  return (root.toString, oleans.size, irs?.map (·.size))

/-- Encodes {name}`m` as described above. -/
def artifactsToJson (m : NameMap ImportArtifacts) : Json := Id.run do
  let mut roots : Array String := #[]
  let mut obj : Std.TreeMap.Raw String Json := ∅
  for (mod, arts) in m do
    if let some (root, numOLeans, numIRs?) := defaultLayout? mod arts then
      -- consecutive entries mostly share their root
      let idx := if roots.back? == some root then roots.size - 1 else
        roots.findIdx? (· == root) |>.getD roots.size
      if idx == roots.size then
        roots := roots.push root
      let counts := #[toJson numOLeans] ++ (numIRs?.map toJson).toArray
      obj := obj.insert mod.toString (Json.arr (#[toJson idx] ++ counts))
    else
      obj := obj.insert mod.toString (toJson arts)
  if !roots.isEmpty then
    obj := obj.insert "" (toJson roots)
  return .obj obj

private def decodeArts (roots : Array System.FilePath) (k : String) (mod : Name) (v : Json) :
    Except String ImportArtifacts := do
  let .arr a := v | fromJson? v
  unless (a.size == 2 || a.size == 3) && a[0]! matches .num _ do
    return ← fromJson? v
  let idx : Nat ← fromJson? a[0]!
  let numOLeans : Nat ← fromJson? a[1]!
  let numIRs? : Option Nat ← if a.size == 3 then some <$> fromJson? a[2]! else pure none
  let some root := roots[idx]?
    | throw s!"invalid root index {idx} for '{k}'"
  unless !mod.isAnonymous && hasOnlyStrComponents mod && numOLeans ≥ 1 &&
      numOLeans ≤ oleanPartExts.size && numIRs?.all (· ≤ irPartExts.size) do
    throw s!"invalid artifacts for '{k}': {v}"
  return .ofArrays <| #[partsAt root mod oleanPartExts numOLeans] ++
    (numIRs?.map (partsAt root mod irPartExts)).toArray

/-- Decodes {name}`artifactsToJson`, as well as the encoding with full paths only. -/
def artifactsFromJson? : Json → Except String (NameMap ImportArtifacts)
  | j@(.obj obj) => do
    let roots : Array System.FilePath ← match j.getObjVal? "" with
      | .ok r => fromJson? r
      | .error _ => pure #[]
    obj.foldlM (init := {}) fun m k v => do
      if k.isEmpty then
        return m
      let mod ← if k == "[anonymous]" then pure .anonymous else
        let n := k.toName
        if n.isAnonymous then throw s!"expected a `Name`, got '{k}'" else pure n
      return m.insert mod (← decodeArts roots k mod v)
  | j => throw s!"expected a `NameMap`, got '{j}'"

-- An indexed setup is not a valid official `ModuleSetup`: its anonymous entry holds the
-- index reference, which official Lean would silently ignore (and then fall back to the
-- search path). A third, non-path marker makes official Lean's `fromJson?` reject the file.
private def indexMarker : String := "paperlean-setup-index"

private def markIndexRef (arts : Json) : Json :=
  match arts.getObjVal? "[anonymous]" with
  | .ok (.arr a) =>
    if a.size == 2 then
      arts.setObjVal! "[anonymous]" (.arr (a.push (.arr #[.str indexMarker, toJson 0])))
    else arts
  | _ => arts

private def stripIndexMarker (json : Json) : Json :=
  match json.getObjVal? "importArts" with
  | .ok arts@(.obj _) =>
    match arts.getObjVal? "[anonymous]" with
    | .ok (.arr a) =>
      if a.size == 3 then
        match a[2]! with
        | .arr m =>
          if m.size == 2 && m[0]! == .str indexMarker && m[1]! matches .num _ then
            json.setObjVal! "importArts" (arts.setObjVal! "[anonymous]" (.arr (a.extract 0 2)))
          else json
        | _ => json
      else json
    | _ => json
  | _ => json

/--
The JSON of a module's setup with {lit}`importArts` encoded compactly (as described for
{lit}`artifactsToJson`), which {lit}`ModuleSetup.load` reads and official Lean does not. A build writes
it to a side file ({lit}`<module>.setup.paperlean`).
-/
def setupToJsonCompact (x : ModuleSetup) : Json :=
  let arts := artifactsToJson x.importArts
  let arts := if x.importArts.contains .anonymous then markIndexRef arts else arts
  (toJson { x with importArts := {} }).setObjVal! "importArts" arts

/-- Like {lit}`fromJson?`, also reading the compact encoding of {lit}`setupToJsonCompact`. -/
def setupFromJsonCompact? (json : Json) : Except String ModuleSetup :=
  let json := stripIndexMarker json
  match json.getObjVal? "importArts" with
  | .ok arts@(.obj o) =>
    if o.contains "" then do
      let setup : ModuleSetup ← fromJson? (json.setObjVal! "importArts" (.obj ∅))
      return { setup with importArts := ← artifactsFromJson? arts }
    else fromJson? json
  | _ => fromJson? json

/-!
Under {lit}`paperlean build`, Lake does not list the artifacts of each module's transitive imports:
it writes an index of the modules whose headers the build read ({lit}`Lake.PaperLean.SetupIndex`),
and the {lit}`importArts` of the setups it writes refer to it with the entry of the anonymous name,
which names no module: {lit}`[[file], [record]]`, the index file and the number of the module's
record in it. {lit}`ModuleSetup.load` then computes the artifacts from the index as Lake does, with
the files at their default location ({lit}`SetupIndex.artifactsAt`); the other entries of
{lit}`importArts` are those of modules whose files are elsewhere, and replace the computed ones.

An index file is named by the hash of its contents ({lit}`SetupIndex.fileName`), which are, with
numbers as 32-bit little-endian integers and strings as their length and UTF-8 bytes:
{lit}`SetupIndex.magic`; the number of roots and the roots; the number of records and the offset of
each record; and per record: the number of components of the module's name and the components, the
module's root, a byte that is 1 for a {lit}`module`, and the number of its imports and per import
the record of the imported module ({lit}`SetupIndex.noModule` if no package of the workspace has it,
{lit}`SetupIndex.unknown` if the index has no record of it) and a byte with {lit}`importAll`,
{lit}`isExported` and {lit}`isMeta` as bits 0, 1 and 2.
-/

namespace SetupIndex

/-- The first bytes of an index, with the version of its format. -/
def magic : String := "paperlean-setup-index 1\n"
def noModule : Nat := 0xffffffff
def unknown : Nat := 0xfffffffe

/-- An import of a module of an index. -/
structure Edge where
  target : Nat
  importAll : Bool
  isExported : Bool
  isMeta : Bool
  deriving Inhabited

/-- A module of an index. -/
structure Record where
  name : Name
  root : Nat
  isModule : Bool
  imports : Array Edge
  deriving Inhabited

/--
The artifacts of the module {name}`mod` below {name}`root` at their default location, as Lake gives
them to its importers ({lit}`Lake.Module.computeExportInfo`), with its {lit}`.olean.private` if
{name}`all`.
-/
def artifactsAt (root : System.FilePath) (mod : Name) (isModule all : Bool) : ImportArtifacts :=
  if isModule then
    .ofArrays #[partsAt root mod oleanPartExts (if all then 3 else 2),
      partsAt root mod irPartExts 2]
  else
    .ofArrays #[partsAt root mod oleanPartExts 1]

private def pushU32 (b : ByteArray) (n : Nat) : ByteArray :=
  b.push n.toUInt8 |>.push (n >>> 8).toUInt8 |>.push (n >>> 16).toUInt8
    |>.push (n >>> 24).toUInt8

private def pushStr (b : ByteArray) (s : String) : ByteArray :=
  pushU32 b s.utf8ByteSize ++ s.toUTF8

private def components : Name → Array String
  | .str p s => (components p).push s
  | _ => #[]

/-- The index of {name}`records`, whose roots are {name}`roots`. -/
def encode (roots : Array String) (records : Array Record) : ByteArray := Id.run do
  let mut table := pushU32 (roots.foldl pushStr (pushU32 magic.toUTF8 roots.size)) records.size
  let start := table.size + 4 * records.size
  let mut recs := ByteArray.empty
  for r in records do
    table := pushU32 table (start + recs.size)
    let cs := components r.name
    recs := cs.foldl pushStr (pushU32 recs cs.size)
    recs := (pushU32 recs r.root).push (if r.isModule then 1 else 0)
    recs := r.imports.foldl (init := pushU32 recs r.imports.size) fun recs e =>
      (pushU32 recs e.target).push <| (if e.importAll then 1 else 0) |||
        (if e.isExported then 2 else 0) ||| (if e.isMeta then 4 else 0)
  return table ++ recs

/-- The name of the file of the index {name}`bytes`. -/
def fileName (bytes : ByteArray) : String :=
  s!"setup-{String.ofList (Nat.toDigits 16 bytes.hash.toNat)}.paperlean"

section
set_option genSizeOf false

/-- A record in an immutable base index, or an immutable single-module file. -/
inductive RecordRef where
  | base (hash : UInt64) (record : Nat)
  | node (hash : UInt64)

/-- The declared module name is checked against the referenced record. An external
import has no workspace record. -/
structure LinkedImport where
  module : Name
  target : Option RecordRef
  importAll : Bool
  isExported : Bool
  isMeta : Bool

structure LinkedRecord where
  name : Name
  root : String
  isModule : Bool
  imports : Array LinkedImport

private def linkedPrefix := "setup-node-"

private def linkedMagic : String := "paperlean-setup-node 1\n"

/-- A node's filename is derived entirely from its bytes. -/
def linkedFileName (hash : UInt64) : String :=
  s!"{linkedPrefix}{String.ofList (Nat.toDigits 16 hash.toNat)}.paperlean"

private def baseFileName (hash : UInt64) : String :=
  s!"setup-{String.ofList (Nat.toDigits 16 hash.toNat)}.paperlean"

private def pushHash (b : ByteArray) (h : UInt64) : ByteArray :=
  pushU32 (pushU32 b h.toNat) (h >>> 32).toNat

private def pushName (b : ByteArray) (n : Name) : ByteArray :=
  let cs := if hasOnlyStrComponents n then components n else #[]
  cs.foldl pushStr (pushU32 b cs.size)

/-- Encodes one module. References contain only a digest and, for a base index, a
record number. Generation paths are never serialized in an edge. -/
def encodeLinked (r : LinkedRecord) : ByteArray := Id.run do
  let b := pushStr (pushName linkedMagic.toUTF8 r.name) r.root
  let b := pushU32 (b.push (if r.isModule then 1 else 0)) r.imports.size
  return r.imports.foldl (init := b) fun b e =>
    let b := pushName b e.module
    let b := b.push <| (if e.importAll then 1 else 0) |||
      (if e.isExported then 2 else 0) ||| (if e.isMeta then 4 else 0)
    match e.target with
    | none => b.push 0
    | some (.base h i) => pushU32 (pushHash (b.push 1) h) i
    | some (.node h) => pushHash (b.push 2) h

end

/-- An index read from a file. -/
structure Index where
  bytes : ByteArray
  roots : Array System.FilePath
  /-- Where the offsets of the records start. -/
  table : Nat
  size : Nat

private def getU8 (b : ByteArray) (i : Nat) : Except String UInt8 :=
  if h : i < b.size then .ok b[i] else .error "it is truncated"

private def getU32 (b : ByteArray) (i : Nat) : Except String Nat :=
  if i + 4 ≤ b.size then
    .ok <| b[i]!.toNat ||| (b[i+1]!.toNat <<< 8) ||| (b[i+2]!.toNat <<< 16) |||
      (b[i+3]!.toNat <<< 24)
  else .error "it is truncated"

private def getStr (b : ByteArray) (i : Nat) : Except String (String × Nat) := do
  let n ← getU32 b i
  unless i + 4 + n ≤ b.size do throw "it is truncated"
  let some s := String.fromUTF8? (b.extract (i + 4) (i + 4 + n))
    | throw "it has a string that is not UTF-8"
  return (s, i + 4 + n)

/-- The prefix of an index through its record count; the offset table need not be present. -/
private def Index.readHeader (bytes : ByteArray) : Except String Index := do
  unless (bytes.extract 0 magic.utf8ByteSize).data == magic.toUTF8.data do
    throw "it is not a setup index of this version"
  let numRoots ← getU32 bytes magic.utf8ByteSize
  let mut i := magic.utf8ByteSize + 4
  let mut roots := #[]
  for _ in [0:numRoots] do
    let (r, j) ← getStr bytes i
    roots := roots.push ⟨r⟩
    i := j
  let size ← getU32 bytes i
  return { bytes, roots, table := i + 4, size }

/-- The index {name}`bytes` read from {name}`file`. Independent or unreceipted files retain this
full content-hash validation path. -/
def Index.read (file : System.FilePath) (bytes : ByteArray) : Except String Index := do
  unless file.fileName == some (fileName bytes) do
    throw "its contents do not have the hash it is named by"
  let ix ← Index.readHeader bytes
  unless ix.table + 4 * ix.size ≤ bytes.size do throw "it is truncated"
  return ix

/-- Decodes one record, from a whole index or an individually read record. -/
private def decodeRecord (b : ByteArray) (start numRoots : Nat) : Except String Record := do
  let mut p := start
  let numComponents ← getU32 b p
  p := p + 4
  let mut name := Name.anonymous
  for _ in [0:numComponents] do
    let (c, q) ← getStr b p
    name := name.str c
    p := q
  let root ← getU32 b p
  unless root < numRoots do throw s!"the record of {name} has no root"
  let isModule := (← getU8 b (p + 4)) == 1
  let numImports ← getU32 b (p + 5)
  p := p + 9
  let mut imports := #[]
  for _ in [0:numImports] do
    let target ← getU32 b p
    let f ← getU8 b (p + 4)
    imports := imports.push
      { target, importAll := f &&& 1 != 0, isExported := f &&& 2 != 0, isMeta := f &&& 4 != 0 }
    p := p + 5
  return { name, root, isModule, imports }

/-- The record {name}`i` of {name}`ix`. -/
def Index.record (ix : Index) (i : Nat) : Except String Record := do
  unless i < ix.size do throw s!"it has no record {i}"
  decodeRecord ix.bytes (← getU32 ix.bytes (ix.table + 4 * i)) ix.roots.size

/-- State only for reached records, independent of the total module count in the index. -/
private structure Walk where
  recs : Std.HashMap Nat (Record × System.FilePath) := {}
  arts : Std.HashMap Nat ImportArtifacts := {}
  allVisited : Std.HashSet Nat := {}
  metaVisited : Std.HashSet Nat := {}
  entries : Array Nat := #[]
  deriving Inhabited

private def Walk.record [Monad m] [MonadExceptOf String m] (w : Walk)
    (read : Nat → m (Record × System.FilePath)) (i : Nat) :
    m ((Record × System.FilePath) × Walk) := do
  if let some r := w.recs[i]? then return (r, w)
  if i == unknown then throw "it has no record of an imported module"
  let r ← read i
  return (r, { w with recs := w.recs.insert i r })

private def Walk.insert (w : Walk) (i : Nat) (r : Record) (root : System.FilePath) (all : Bool) : Walk :=
  let arts := artifactsAt root r.name r.isModule all
  if !w.arts.contains i then
    { w with entries := w.entries.push i, arts := w.arts.insert i arts }
  else
    { w with arts := w.arts.insert i arts }

/-- {lit}`enqueue` of {lit}`Lake.fetchTransImportArts`: pushes the imports of {name}`r` that the
walk visits. -/
private def enqueue (nonModule importAll needsMeta : Bool) (r : Record)
    (q : Array (Nat × Bool × Bool)) : Array (Nat × Bool × Bool) :=
  r.imports.foldr (init := q) fun e q =>
    if e.target == noModule then q else
    let reachable := importAll || e.isExported
    let importAll := nonModule || (importAll && e.importAll)
    let needsMeta := needsMeta || (reachable && e.isMeta)
    if reachable || needsMeta then q.push (e.target, importAll, needsMeta) else q

/-- {lit}`walk` of {lit}`Lake.fetchTransImportArts`, shared by full and demand readers. -/
private partial def Walk.walk [Monad m] [MonadExceptOf String m] (w : Walk)
    (read : Nat → m (Record × System.FilePath)) (nonModule : Bool)
    (q : Array (Nat × Bool × Bool)) : m Walk := do
  let some (i, importAll, needsMeta) := q.back? | return w
  let q := q.pop
  let ((r, root), w) ← w.record read i
  let doAll := importAll && !w.allVisited.contains i
  let doMeta := needsMeta && !w.metaVisited.contains i
  let existing? := w.arts[i]?
  if let some a := existing? then
    unless a.oleanServer?.isSome && (doAll || doMeta) do return ← w.walk read nonModule q
  let w := { w with
    allVisited := if importAll then w.allVisited.insert i else w.allVisited
    metaVisited := if needsMeta then w.metaVisited.insert i else w.metaVisited }
  let wantAll := w.allVisited.contains i || existing?.any (·.oleanPrivate?.isSome)
  (w.insert i r root wantAll).walk read nonModule (enqueue nonModule importAll needsMeta r q)

/-- Replays Lake's direct-import and transitive visibility rules with a record reader. -/
private def importArtsWith [Monad m] [MonadExceptOf String m]
    (read : Nat → m (Record × System.FilePath)) (mod : Name) (i : Nat) :
    m (NameMap ImportArtifacts) := do
  let ((root, _), w) ← Walk.record {} read i
  unless root.name == mod do throw s!"its record {i} is not of {mod}"
  let nonModule := !root.isModule
  let w ← root.imports.foldlM (init := w) fun w e => do
    if e.target == noModule then return w
    let ((r, path), w) ← w.record read e.target
    let all := nonModule || e.importAll
    -- (an entry is only replaced by one with `.olean.private`)
    if w.arts.contains e.target && !all then return w
    return w.insert e.target r path all
  let (q, w) ← root.imports.foldrM (init := (#[], w)) fun e (q, w) => do
    if e.target == noModule then return (q, w)
    let ((r, _), w) ← w.record read e.target
    return (enqueue nonModule (nonModule || e.importAll) e.isMeta r q, w)
  let w ← w.walk read nonModule q
  return w.entries.foldl (init := {}) fun m j => m.insert w.recs[j]!.1.name w.arts[j]!

/--
The artifacts of the transitive imports of {name}`mod`, whose record is {name}`i`: those of
{lit}`Lake.fetchImportInfo` for its direct imports, then those that {lit}`Lake.fetchTransImportArts`
adds, whose steps this follows, with all files at their default location. Storage is proportional to
records reached, even on the independent full-validation path.
-/
def Index.importArts (ix : Index) (mod : Name) (i : Nat) :
    Except String (NameMap ImportArtifacts) :=
  importArtsWith (fun j => do
    let r ← ix.record j
    return (r, ix.roots[r.root]!)) mod i

/-- An owned read-only descriptor of a writer-validated immutable generation. -/
private opaque DemandIndex : Type := Unit

/-- Publishes a v1 index without overwriting an existing generation. For larger indices the
native writer reads back and compares the file to {name}`bytes` before publishing an identity
receipt. Small indices use full content-hash validation. Returns false on platforms without the demand reader. -/
@[extern "lean_paperlean_setup_index_publish"]
opaque publish (file : @& String) (bytes : @& ByteArray) : IO Bool

@[extern "lean_paperlean_setup_index_open"]
private opaque openDemand (file : @& String) : IO (Option (DemandIndex × ByteArray))

@[extern "lean_paperlean_setup_index_record"]
private opaque readDemand (index : @& DemandIndex) (i : @& Nat) : IO ByteArray

@[extern "lean_paperlean_setup_index_check"]
private opaque checkDemand (index : @& DemandIndex) : IO Unit

@[extern "lean_paperlean_setup_index_close"]
private opaque closeDemand (index : @& DemandIndex) : BaseIO Unit

/-- Demand reading is available only for the exact opened file covered by a complete receipt.
Missing or stale receipts choose full validation; an opened generation changing during traversal
is rejected. The handle is closed on both successful and exceptional exits. -/
private def demandImportArts (file : System.FilePath) (mod : Name) (i : Nat) :
    IO (Option (Except String (NameMap ImportArtifacts))) := do
  let opened ← openDemand file.toString
  let some (handle, headerBytes) := opened | return none
  try
    let action : ExceptT String IO (NameMap ImportArtifacts) := do
      let ix ← liftExcept (Index.readHeader headerBytes)
      let read (j : Nat) : ExceptT String IO (Record × System.FilePath) := do
        let bytes ← readDemand handle j
        let r ← liftExcept (decodeRecord bytes 0 ix.roots.size)
        return (r, ix.roots[r.root]!)
      let arts ← importArtsWith read mod i
      checkDemand handle
      return arts
    return some (← action.run)
  finally
    closeDemand handle


section
set_option genSizeOf false

-- Quoted module components can contain punctuation and path separators. They are
-- used exactly as in v1 artifact paths. Paths to other index files use only digests.
private def validLinkedPart (c : String) : Bool := !c.toUTF8.data.contains 0

private def getName (b : ByteArray) (pos : Nat) : Except String (Name × Nat) := do
  let count ← getU32 b pos
  unless count > 0 && count ≤ (b.size - (pos + 4)) / 4 do throw "invalid module name"
  let mut n := Name.anonymous
  let mut p := pos + 4
  for _ in [0:count] do
    let (c, next) ← getStr b p
    unless validLinkedPart c do throw "invalid module name component"
    n := n.str c
    p := next
  return (n, p)

private def getHash (b : ByteArray) (i : Nat) : Except String UInt64 := do
  let lo ← getU32 b i
  let hi ← getU32 b (i + 4)
  return lo.toUInt64 ||| (hi.toUInt64 <<< 32)

/-- Decode exactly one node. Its edge tags contain digest values, never filenames. -/
private def decodeLinked (bytes : ByteArray) : Except String LinkedRecord := do
  let m := linkedMagic.toUTF8
  unless (bytes.extract 0 m.size).data == m.data do throw "unrecognized setup node version"
  let (name, p) ← getName bytes m.size
  let (root, p) ← getStr bytes p
  if root.toUTF8.data.contains 0 then throw "invalid root"
  let flag ← getU8 bytes p
  if flag > 1 then throw "invalid module flag"
  let count ← getU32 bytes (p + 1)
  let mut p := p + 5
  let mut imports : Array LinkedImport := #[]
  for _ in [0:count] do
    let (module, q) ← getName bytes p
    let f ← getU8 bytes q
    if f > 7 then throw "invalid import flags"
    let (target, next) ← match ← getU8 bytes (q + 1) with
      | 0 => pure (none, q + 2)
      | 1 => do
        let h ← getHash bytes (q + 2)
        let i ← getU32 bytes (q + 10)
        pure (some (RecordRef.base h i), q + 14)
      | 2 => do
        let h ← getHash bytes (q + 2)
        pure (some (RecordRef.node h), q + 10)
      | _ => throw "unknown import reference tag"
    imports := imports.push {
      module, target, importAll := f &&& 1 != 0, isExported := f &&& 2 != 0, isMeta := f &&& 4 != 0 }
    p := next
  unless p == bytes.size do throw "unexpected trailing node bytes"
  return {name, root, isModule := flag == 1, imports}

private def RecordRef.key : RecordRef → Bool × UInt64 × Nat
  | .node h => (true, h, 0)
  | .base h i => (false, h, i)

/-- Translates immutable content references to the compact traversal IDs used by
{lit}`Walk`. One logical module must resolve to the same record on every path. -/
private structure LinkedGraph where
  ids : Std.HashMap (Bool × UInt64 × Nat) Nat := {}
  refs : Array (RecordRef × Option Name) := #[]
  names : NameMap Nat := {}

private def LinkedGraph.checkName (g : LinkedGraph) (i : Nat) (name : Name) :
    Except String LinkedGraph := do
  let some (ref, expected?) := g.refs[i]? | throw "missing internal record"
  if let some expected := expected? then
    unless expected == name do throw s!"record {i} expected {expected} but contains {name}"
  if let some previous := g.names.find? name then
    if previous != i then throw s!"conflicting setup records for {name}"
    return g
  return {g with refs := g.refs.setIfInBounds i (ref, some name), names := g.names.insert name i}

private def LinkedGraph.intern (g : LinkedGraph) (ref : RecordRef) (name? : Option Name) :
    Except String (Nat × LinkedGraph) := do
  let (i, g) ← match g.ids[ref.key]? with
    | some i => pure (i, g)
    | none => do
      let i := g.refs.size
      if i ≥ unknown then throw "too many reached records"
      pure (i, {g with ids := g.ids.insert ref.key i, refs := g.refs.push (ref, none)})
  let g ← match name? with | some name => g.checkName i name | none => pure g
  return (i, g)

private abbrev ReadLinked := ExceptT String IO

private def internRef (graph : IO.Ref LinkedGraph) (ref : RecordRef) (name? : Option Name) :
    ReadLinked Nat := do
  liftExcept (← graph.modifyGet fun g =>
    match g.intern ref name? with
    | .ok (i, next) => (.ok i, next)
    | .error e => (.error e, {}))

private structure Segment where
  index : Index
  handle? : Option DemandIndex

/-- Read a stable regular file from a single descriptor, returning its total size and
at most {name}`limit` bytes. Platforms without this primitive return {lit}`none`. -/
@[extern "lean_paperlean_setup_read_regular"]
opaque readRegularPrefix (file : @& String) (limit : USize) : IO (Option (UInt64 × ByteArray))

private def readRegularFile (path : System.FilePath) : IO ByteArray := do
  if let some (size, bytes) ← readRegularPrefix path.toString (USize.size - 1).toUSize then
    unless size.toNat == bytes.size do throw <| IO.userError "incomplete setup file"
    return bytes
  unless (← path.symlinkMetadata).type == .file do throw <| IO.userError "expected a regular setup file"
  IO.FS.readBinFile path

/-- Independent v1 indexes may be symlinks. Resolve a link only after the normal
descriptor read declined it. The caller validates bytes against the original filename. -/
private def readV1File (file : System.FilePath) : IO ByteArray := do
  try readRegularFile file catch e =>
    let .ok st ← file.symlinkMetadata.toBaseIO | throw e
    unless st.type == .symlink do throw e
    readRegularFile (← IO.FS.realPath file)

/-- Unreceipted v1 segments retain their original full content validation. Receipted
segments keep a descriptor through the entire walk and read only reached records. -/
private def openSegment (segments : IO.Ref (Std.HashMap UInt64 Segment)) (dir : System.FilePath)
    (hash : UInt64) : ReadLinked Segment := do
  if let some seg := (← segments.get)[hash]? then return seg
  let path := dir / baseFileName hash
  let seg ← match ← openDemand path.toString with
    | some (h, bytes) => do
      match Index.readHeader bytes with
      | .ok ix => pure { index := ix, handle? := some h }
      | .error e => do closeDemand h; throw e
    | none => do
      let bytes ← readV1File path
      let ix ← liftExcept (Index.read path bytes)
      pure {index := ix, handle? := none}
  segments.modify (·.insert hash seg)
  return seg

private def readLinkedFile (file : System.FilePath) : IO ByteArray := do
  let bytes ← readRegularFile file
  unless file.fileName == some (linkedFileName bytes.hash) do
    throw <| IO.userError "setup node contents do not match its filename"
  return bytes

private def readLinkedRef (graph : IO.Ref LinkedGraph) (segments : IO.Ref (Std.HashMap UInt64 Segment))
    (dir : System.FilePath) (rootHash : UInt64) (root : LinkedRecord) (i : Nat) :
    ReadLinked (Record × System.FilePath) := do
  let some (ref, _) := (← graph.get).refs[i]? | throw "missing linked reference"
  let (record, path) ← match ref with
    | .node hash => do
      let r ← if hash == rootHash then pure root else do
        liftExcept (decodeLinked (← readLinkedFile (dir / linkedFileName hash)))
      let imports ← r.imports.mapM fun e => do
        let target ← match e.target with
          | none => pure noModule
          | some ref => internRef graph ref (some e.module)
        pure {target, importAll := e.importAll, isExported := e.isExported, isMeta := e.isMeta : Edge}
      pure ({name := r.name, root := 0, isModule := r.isModule, imports : Record}, ⟨r.root⟩)
    | .base hash j => do
      let seg ← openSegment segments dir hash
      let r ← match seg.handle? with
        | some h => do
          let bytes ← readDemand h j
          liftExcept (decodeRecord bytes 0 seg.index.roots.size)
        | none => liftExcept (seg.index.record j)
      unless !r.name.isAnonymous && hasOnlyStrComponents r.name && (components r.name).all validLinkedPart do
        throw "invalid module name in base record"
      let imports ← r.imports.mapM fun e => do
        if e.target == unknown || e.target == noModule then return e
        return {e with target := ← internRef graph (.base hash e.target) none}
      pure ({r with imports}, seg.index.roots[r.root]!)
  liftExcept (← graph.modifyGet fun g =>
    match g.checkName i record.name with
    | .ok next => (.ok (), next)
    | .error e => (.error e, {}))
  return (record, path)

private def isLinkedFile (file : System.FilePath) : Bool :=
  file.fileName.any fun s => (s.toUTF8.extract 0 linkedPrefix.utf8ByteSize).data == linkedPrefix.toUTF8.data

private def linkedImportArts (file : System.FilePath) (mod : Name) (i : Nat) :
    IO (Except String (NameMap ImportArtifacts)) := do
  if i != 0 then return .error "a node contains only record zero"
  let bytes ← readLinkedFile file
  let root ← match decodeLinked bytes with
    | .ok r => pure r
    | .error e => return .error e
  let dir := file.parent.getD "."
  let graph ← IO.mkRef ({} : LinkedGraph)
  let segments ← IO.mkRef (∅ : Std.HashMap UInt64 Segment)
  try
    let action : ReadLinked (NameMap ImportArtifacts) := do
      let i ← internRef graph (.node bytes.hash) (some mod)
      let arts ← importArtsWith (readLinkedRef graph segments dir bytes.hash root) mod i
      for (_, seg) in ← segments.get do
        if let some h := seg.handle? then checkDemand h
      return arts
    action.run
  finally
    for (_, seg) in ← segments.get do
      if let some h := seg.handle? then closeDemand h

end

/-- The entry of the anonymous name in {lit}`importArts` that refers to record {name}`i` of the
index {name}`file`. -/
def reference (file : System.FilePath) (i : Nat) : ImportArtifacts :=
  .ofArrays #[#[file], #[toString i]]

/-- Whether {name}`setup` refers to a setup index. -/
def refersToIndex (setup : ModuleSetup) : Bool :=
  setup.importArts.contains .anonymous

end SetupIndex

/--
{name}`setup` with the artifacts of its module's transitive imports from the setup index that its
{lit}`importArts` refer to, if they do.
-/
@[noinline, nospecialize] def withSetupIndex (setup : ModuleSetup) : IO (Except String ModuleSetup) := do
  let some ref := setup.importArts.find? .anonymous | return .ok setup
  let some file := ref.toArrays[0]?.bind (·[0]?) | return .error "it refers to no setup index"
  let some record := ref.toArrays[1]?.bind (·[0]?) | return .error "it refers to no record"
  let .ok i := Json.parse record.toString >>= fromJson? (α := Nat)
    | return .error "it refers to no record"
  let resolved ← if SetupIndex.isLinkedFile file then
    match ← (SetupIndex.linkedImportArts file setup.name i).toBaseIO with
    | .ok r => pure r
    | .error e => pure (.error (toString e))
  else match ← (SetupIndex.demandImportArts file setup.name i).toBaseIO with
    | .ok (some r) => pure r
    | .error e => pure (.error s!"cannot read its immutable generation ({e})")
    | .ok none =>
      let bytes ← match ← (SetupIndex.readV1File file).toBaseIO with
        | .ok bytes => pure bytes
        | .error e => return .error s!"its setup index {file} cannot be read ({e}); a setup that \
            refers to one is only valid during the build that wrote it"
      pure <| (SetupIndex.Index.read file bytes).bind (·.importArts setup.name i)
  match resolved with
  | .ok arts => return .ok { setup with importArts :=
      (setup.importArts.erase .anonymous).foldl (init := arts) fun m n a => m.insert n a }
  | .error e => return .error s!"its setup index {file} is damaged: {e}"

/-- The setup in the JSON {name}`contents`, as {lit}`ModuleSetup.load` reads it. -/
def setupOfJson (contents : String) : IO (Except String ModuleSetup) :=
  match Json.parse contents >>= setupFromJsonCompact? with
  | .ok setup => withSetupIndex setup
  | .error e => return .error e

end PaperLean

/-- Load a {lean}`ModuleSetup` from a JSON file. -/
-- PaperLean: (not inlined: its body calls PaperLean's code)
@[noinline] def ModuleSetup.load (path : System.FilePath) : IO ModuleSetup := do
  let contents ← IO.FS.readFile path
  match ← PaperLean.setupOfJson contents with
  | .ok info => pure info
  | .error msg => throw <| IO.userError s!"failed to load header from {path}: {msg}"
-- Modified by PaperLean.
