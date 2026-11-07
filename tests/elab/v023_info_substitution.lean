import Lean

open Lean Elab

private structure Marker where
  n : Nat
  deriving TypeName

private def marker : Info :=
  .ofCustomInfo { stx := .missing, value := Dynamic.mk (Marker.mk 7) }

private def isHole (n : Name) : InfoTree → Bool
  | .hole id => id.name == n
  | _ => false

#eval show IO Unit from do
  let a : MVarId := ⟨`a⟩
  let b : MVarId := ⟨`b⟩
  let c : MVarId := ⟨`c⟩
  let tree := InfoTree.node marker ((PersistentArray.empty : PersistentArray InfoTree).push (.hole a) |>.push (.hole c))
  let empty : PersistentHashMap MVarId InfoTree := {}
  match tree.substitute empty with
  | .node _ children =>
    unless children.size == 2 && isHole `a children[0]! && isHole `c children[1]! do
      throw <| IO.userError "empty substitution changed a tree"
  | _ => throw <| IO.userError "empty substitution changed the root"
  let assignment := empty.insert a (.hole b) |>.insert b (.node marker {})
  match tree.substitute assignment with
  | .node _ children =>
    unless children.size == 2 && isHole `c children[1]! do
      throw <| IO.userError "nonempty substitution lost children"
    match children[0]! with
    | .node _ cs => unless cs.isEmpty do throw <| IO.userError "wrong replacement"
    | _ => throw <| IO.userError "transitive assignment was not substituted"
  | _ => throw <| IO.userError "nonempty substitution changed the root"
  let p ← IO.Promise.new (α := InfoTree)
  let info : InfoState := { trees := PersistentArray.empty.push tree, lazyAssignment := ({} : PersistentHashMap MVarId (Task InfoTree)).insert a p.result! }
  let result := info.substituteLazy
  p.resolve (.hole b)
  let result := result.get
  unless result.lazyAssignment.isEmpty do throw <| IO.userError "lazy assignment was retained"
  match result.trees[0]! with
  | .node _ children =>
    unless isHole `b children[0]! do throw <| IO.userError "lazy assignment was ignored"
  | _ => throw <| IO.userError "lazy substitution changed the root"
