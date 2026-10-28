/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mac Malone
-/
module

prelude
public import Lean.Data.Json.Parser
public import Lean.Util.LeanOptions
import Lean.Util.Path

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

/-!
Lake lists the artifacts of every transitively imported module, so these maps can have tens of
thousands of entries. An entry whose files are a prefix of the usual parts at their default location
below a package root ({lit}`modToFilePath root mod ext`) is therefore encoded as
{lit}`[root, numOLeanParts]` or {lit}`[root, numOLeanParts, numIRParts]`, where {lit}`root` indexes
the array of roots stored under the key {lit}`""` (which cannot name a module). All other entries
keep their full paths.
-/

private def oleanPartExts : Array String := #["olean", "olean.server", "olean.private"]
private def irPartExts : Array String := #["ir.sig", "ir"]

private def hasOnlyStrComponents : Name → Bool
  | .anonymous => true
  | .str p _ => hasOnlyStrComponents p
  | .num .. => false

private def partsAt (root : System.FilePath) (mod : Name) (exts : Array String) (n : Nat) :
    Array System.FilePath :=
  let stem := (modToFilePath root mod "").toString
  (exts.extract 0 n).map fun ext => ⟨stem ++ "." ++ ext⟩

/--
If the files of {name}`arts` are at their default location for {name}`mod`, returns their root and
the number of olean parts and, if there is a second array, of IR parts.
-/
private def ImportArtifacts.defaultLayout? (mod : Name) (arts : ImportArtifacts) :
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
def ImportArtifacts.mapToJson (m : NameMap ImportArtifacts) : Json := Id.run do
  let mut roots : Array String := #[]
  let mut obj : Std.TreeMap.Raw String Json := ∅
  for (mod, arts) in m do
    if let some (root, numOLeans, numIRs?) := arts.defaultLayout? mod then
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

/-- Decodes {name}`ImportArtifacts.mapToJson`, as well as the encoding with full paths only. -/
def ImportArtifacts.mapFromJson? : Json → Except String (NameMap ImportArtifacts)
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

instance : ToJson (NameMap ImportArtifacts) := ⟨ImportArtifacts.mapToJson⟩
instance : FromJson (NameMap ImportArtifacts) := ⟨ImportArtifacts.mapFromJson?⟩

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

/-- Load a {lean}`ModuleSetup` from a JSON file. -/
def ModuleSetup.load (path : System.FilePath) : IO ModuleSetup := do
  let contents ← IO.FS.readFile path
  match Json.parse contents >>= fromJson? with
  | .ok info => pure info
  | .error msg => throw <| IO.userError s!"failed to load header from {path}: {msg}"
-- Modified by PaperLean.
