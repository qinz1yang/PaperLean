/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mac Malone
-/
module

prelude
public import Lean.Data.Json.Parser
public import Lean.Util.LeanOptions

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

/--
The JSON of a module's setup with {lit}`importArts` encoded compactly (as described for
{lit}`artifactsToJson`), which {lit}`ModuleSetup.load` reads and official Lean does not. A build writes
it to a side file ({lit}`<module>.setup.paperlean`).
-/
def setupToJsonCompact (x : ModuleSetup) : Json :=
  (toJson { x with importArts := {} }).setObjVal! "importArts" (artifactsToJson x.importArts)

/-- Like {lit}`fromJson?`, also reading the compact encoding of {lit}`setupToJsonCompact`. -/
def setupFromJsonCompact? (json : Json) : Except String ModuleSetup :=
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

/-- The index {name}`bytes` read from {name}`file`. -/
def Index.read (file : System.FilePath) (bytes : ByteArray) : Except String Index := do
  unless file.fileName == some (fileName bytes) do
    throw "its contents do not have the hash it is named by"
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
  unless i + 4 + 4 * size ≤ bytes.size do throw "it is truncated"
  return { bytes, roots, table := i + 4, size }

/-- The record {name}`i` of {name}`ix`. -/
def Index.record (ix : Index) (i : Nat) : Except String Record := do
  unless i < ix.size do throw s!"it has no record {i}"
  let b := ix.bytes
  let mut p ← getU32 b (ix.table + 4 * i)
  let numComponents ← getU32 b p
  p := p + 4
  let mut name := Name.anonymous
  for _ in [0:numComponents] do
    let (c, q) ← getStr b p
    name := name.str c
    p := q
  let root ← getU32 b p
  unless root < ix.roots.size do throw s!"the record of {name} has no root"
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

/-- The state of {lit}`Index.importArts`: per record, the record once decoded, its entry, and
whether the walk visited it for {lit}`import all` and for {lit}`meta`; and the records with an
entry. -/
private structure Walk where
  recs : Array (Option Record)
  arts : Array (Option ImportArtifacts)
  allVisited : Array Bool
  metaVisited : Array Bool
  entries : Array Nat := #[]

private def Walk.record (w : Walk) (ix : Index) (i : Nat) : Except String (Record × Walk) := do
  if let some (some r) := w.recs[i]? then return (r, w)
  if i == unknown then throw "it has no record of an imported module"
  let r ← ix.record i
  return (r, { w with recs := w.recs.set! i (some r) })

private def Walk.insert (w : Walk) (ix : Index) (i : Nat) (r : Record) (all : Bool) : Walk :=
  let arts := some (artifactsAt ix.roots[r.root]! r.name r.isModule all)
  -- Inspect the old slot before updating it, so the update need not copy the array.
  if w.arts[i]!.isNone then
    { w with entries := w.entries.push i, arts := w.arts.set! i arts }
  else
    { w with arts := w.arts.set! i arts }

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

/-- {lit}`walk` of {lit}`Lake.fetchTransImportArts`. -/
private partial def Walk.walk (w : Walk) (ix : Index) (nonModule : Bool)
    (q : Array (Nat × Bool × Bool)) : Except String Walk := do
  let some (m, importAll, needsMeta) := q.back? | return w
  let q := q.pop
  let (r, w) ← w.record ix m
  let doAll := importAll && !w.allVisited[m]!
  let doMeta := needsMeta && !w.metaVisited[m]!
  let existing? := w.arts[m]!
  if let some a := existing? then
    unless a.oleanServer?.isSome && (doAll || doMeta) do return ← w.walk ix nonModule q
  let w := { w with
    allVisited := if importAll then w.allVisited.set! m true else w.allVisited
    metaVisited := if needsMeta then w.metaVisited.set! m true else w.metaVisited }
  let wantAll := w.allVisited[m]! || existing?.any (·.oleanPrivate?.isSome)
  (w.insert ix m r wantAll).walk ix nonModule (enqueue nonModule importAll needsMeta r q)

/--
The artifacts of the transitive imports of {name}`mod`, whose record is {name}`i`: those of
{lit}`Lake.fetchImportInfo` for its direct imports, then those that {lit}`Lake.fetchTransImportArts`
adds, whose steps this follows, with all files at their default location.
-/
def Index.importArts (ix : Index) (mod : Name) (i : Nat) :
    Except String (NameMap ImportArtifacts) := do
  let n := ix.size
  let w : Walk := { recs := .replicate n none, arts := .replicate n none,
                    allVisited := .replicate n false, metaVisited := .replicate n false }
  let (root, w) ← w.record ix i
  unless root.name == mod do throw s!"its record {i} is not of {mod}"
  let nonModule := !root.isModule
  let w ← root.imports.foldlM (init := w) fun w e => do
    if e.target == noModule then return w
    let (r, w) ← w.record ix e.target
    let all := nonModule || e.importAll
    -- (an entry is only replaced by one with `.olean.private`)
    if w.arts[e.target]!.isSome && !all then return w
    return w.insert ix e.target r all
  let (q, w) ← root.imports.foldrM (init := (#[], w)) fun e (q, w) => do
    if e.target == noModule then return (q, w)
    let (r, w) ← w.record ix e.target
    return (enqueue nonModule (nonModule || e.importAll) e.isMeta r q, w)
  let w ← w.walk ix nonModule q
  return w.entries.foldl (init := {}) fun m j => m.insert (w.recs[j]!.get!).name (w.arts[j]!.get!)

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
def withSetupIndex (setup : ModuleSetup) : IO (Except String ModuleSetup) := do
  let some ref := setup.importArts.find? .anonymous | return .ok setup
  let some file := ref.toArrays[0]?.bind (·[0]?) | return .error "it refers to no setup index"
  let some record := ref.toArrays[1]?.bind (·[0]?) | return .error "it refers to no record"
  let .ok i := Json.parse record.toString >>= fromJson? (α := Nat)
    | return .error "it refers to no record"
  let bytes ← match ← (IO.FS.readBinFile file).toBaseIO with
    | .ok bytes => pure bytes
    | .error e => return .error s!"its setup index {file} cannot be read ({e}); a setup that \
        refers to one is only valid during the build that wrote it"
  match (SetupIndex.Index.read file bytes).bind (·.importArts setup.name i) with
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
