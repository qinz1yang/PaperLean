/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
import all Lean.Meta.DiscrTree.Basic
public import Lean.Meta.Tactic.Simp.SimpTheorems
public import Lean.Meta.Instances
import Lean.PaperLean.GraphDiff

/-!
The imported states of simp sets and of the instance extension, replayed by
`paperlean/import_state.cpp` instead of folded, which `ScopedEnvExtension.addImportedFn` calls
through a hook. The functions exported here are those the replay calls for entries that no import
image (`writeImportImage`) describes.
-/

namespace Lean.PaperLean
open Meta

@[export lean_paperlean_discr_tree_key_lt]
private def keyLtForImport (a b : DiscrTree.Key) : Bool := a < b
@[export lean_paperlean_discr_tree_key_hash]
private def keyHashForImport (k : DiscrTree.Key) : UInt64 := k.hash
@[export lean_paperlean_discr_tree_key_beq]
private def keyBEqForImport (a b : DiscrTree.Key) : Bool := a == b
/-- `createNodes #[k, k] v 1`, whose two nodes hold the arrays `createNodes` starts nodes with. -/
@[export lean_paperlean_discr_tree_create_nodes_probe]
private def createNodesProbe (k : DiscrTree.Key) (v : Nat) : DiscrTree.Trie Nat :=
  DiscrTree.createNodes #[k, k] v 1

@[export lean_paperlean_simp_theorem_keys]
private def simpTheoremKeysForImport (t : SimpTheorem) : Array SimpTheoremKey := t.keys
@[export lean_paperlean_simp_theorem_post]
private def simpTheoremPostForImport (t : SimpTheorem) : Bool := t.post
@[export lean_paperlean_simp_theorem_proof]
private def simpTheoremProofForImport (t : SimpTheorem) : Expr := t.proof
@[export lean_paperlean_simp_theorem_origin]
private def simpTheoremOriginForImport (t : SimpTheorem) : Origin := t.origin
@[export lean_paperlean_origin_hash]
private def originHashForImport (o : Origin) : UInt64 := hash o
/-- With `Origin.key`, what `==` on origins compares: 1 or 2 for `.decl` with `inv` false or true. -/
@[export lean_paperlean_origin_kind]
private def originKindForImport (o : Origin) : UInt8 :=
  match o with
  | .decl _ _ false => 1
  | .decl _ _ true => 2
  | _ => 0
@[export lean_paperlean_origin_key]
private def originKeyForImport (o : Origin) : Name := o.key
@[export lean_paperlean_origin_converse]
private def originConverseForImport (o : Origin) : Option Origin := o.converse
/-- The origins that `SimpTheorems.eraseCore` erases for the equation theorems of a declaration. -/
@[export lean_paperlean_origin_mk_eqn]
private def mkEqnOriginForImport (n : Name) : Origin := .decl n true (inv := false)

@[export lean_paperlean_instance_entry_keys]
private def instanceEntryKeysForImport (e : InstanceEntry) : Array InstanceKey := e.keys
@[export lean_paperlean_instance_entry_val]
private def instanceEntryValForImport (e : InstanceEntry) : Expr := e.val
@[export lean_paperlean_instance_entry_global_name]
private def instanceEntryGlobalNameForImport (e : InstanceEntry) : Option Name := e.globalName?

/-- The kinds of the extensions whose states are replayed: 0 for simp sets, 1 for instances. -/
private def importedStateKinds : BaseIO (Array (Name × UInt8)) := do
  let mut kinds := #[(instanceExtension.ext.name, (1 : UInt8))]
  for (_, ext) in ← simpExtensionMapRef.get do
    kinds := kinds.push (ext.ext.name, 0)
  return kinds

/-- The kind of the extension named `extName` for the replay, 255 if it is not replayed. -/
@[export lean_paperlean_imported_state_kind]
private def importedStateKind (extName : Name) : BaseIO UInt8 := do
  return (← importedStateKinds).find? (·.1 == extName) |>.map (·.2) |>.getD 255

private def runInitial {σ : Type} (mkInitial : IO σ) : BaseIO (Option NonScalar) := do
  match ← mkInitial.toBaseIO with
  | .ok s => return some (unsafe unsafeCast s)
  | .error _ => return none

/--
The initial state of the extension named `extName`, from its description's `mkInitial`, if its
state is replayed.
-/
@[export lean_paperlean_imported_state_initial]
private def importedStateInitial (extName : Name) : BaseIO (Option NonScalar) := do
  if extName == instanceExtension.ext.name then
    return ← runInitial instanceExtension.descr.mkInitial
  for (_, ext) in ← simpExtensionMapRef.get do
    if ext.ext.name == extName then
      return ← runInitial ext.descr.mkInitial
  return none

/-- Lets `ScopedEnvExtension.addImportedFn` use the replay, which needs this module's state. -/
@[extern "lean_paperlean_enable_imported_state_replay"]
private opaque enableImportedStateReplay : BaseIO Unit

builtin_initialize enableImportedStateReplay

-- monomorphic, as exported functions keep erased parameters in their signature
@[export lean_paperlean_check_imported_state]
private def checkImportedStateImpl (extName : Name) (fast fold : NonScalar) : IO Unit := do
  if let some d := unsafe graphDiff fast fold true then
    throw <| IO.userError s!"PAPERLEAN_IMPORT=check: the imported state of {extName} differs from the fold: {d}"

@[extern "lean_paperlean_write_import_image"]
private opaque writeImportImageCore (out : @& String) (exts : @& Array (Name × UInt8)) : IO Nat

/--
Writes an import image of the first olean pack in use (`LEAN_OLEAN_PACK`) to `out` and returns the
number of entries in it: the entries of every packed module for the simp sets registered so far (for
example by importing the modules that define them) and for the instance extension, in the form in
which importing builds their states. Setting `LEAN_IMPORT_IMAGE` to the image makes imports use it
for the entries of packed modules; an image written for another pack, by another version or damaged
is ignored with a warning.
-/
public def writeImportImage (out : System.FilePath) : IO Nat := do
  writeImportImageCore out.toString (← importedStateKinds)

end Lean.PaperLean
