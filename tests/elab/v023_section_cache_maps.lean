module
public import Lean
import all Lean.Meta.Basic
import all Lean.PaperLean.SectionVars
open Lean Meta PaperLean.SectionVars

-- Frozen 9854b799 map rebuild, without semantic edits.
private unsafe def referenceRmCache (c : Meta.Cache) : RemapM Meta.Cache := do
  let inferType ← c.inferType.foldlM (init := {}) fun acc k v =>
    return acc.insert { k with expr := ← rmExpr k.expr } (← rmExpr v)
  -- (few keys of these have identifiers: `whnf` caches closed terms, `funInfo` mostly constants)
  let whnf ← c.whnf.foldlM (init := c.whnf) fun acc k v => do
    let hasId := fun (x : Expr) => x.hasFVar || x.hasMVar
    if hasId k.expr then
      return (acc.erase k).insert { k with expr := ← rmExpr k.expr } (← rmExpr v)
    else if hasId v then
      return acc.insert k (← rmExpr v)
    else
      return acc
  let funInfo ← c.funInfo.foldlM (init := c.funInfo) fun acc k v => do
    if k.expr.hasFVar || k.expr.hasMVar then
      return (acc.erase k).insert { k with expr := ← rmExpr k.expr } v
    else
      return acc
  let synthInstance ← c.synthInstance.foldlM (init := {}) fun acc k v => do
    let k' := { k with type := ← rmExpr k.type, localInsts := ← rmLocalInsts k.localInsts }
    let v' ← v.mapM fun r => return { r with
      expr := ← rmExpr r.expr, mvars := ← r.mvars.mapM rmExpr }
    return acc.insert k' v'
  return { c with inferType, whnf, funInfo, synthInstance }


private def exactResult (a b : Option AbstractMVarsResult) : Bool :=
  match a, b with
  | some a, some b => a.paramNames == b.paramNames && a.expr.equal b.expr &&
    a.mvars.size == b.mvars.size && (a.mvars.zip b.mvars).all fun (x, y) => x.equal y
  | none, none => true
  | _, _ => false

private def exactCaches (a b : Meta.Cache) : Bool :=
  a.inferType.toList.length == b.inferType.toList.length &&
  a.inferType.foldl (init := true) (fun ok k v => ok &&
    (b.inferType.findEntry? k).any fun (k', v') =>
      k.configKey == k'.configKey && k.expr.equal k'.expr && v.equal v') &&
  a.synthInstance.toList.length == b.synthInstance.toList.length &&
  a.synthInstance.foldl (init := true) (fun ok k v => ok &&
    (b.synthInstance.findEntry? k).any fun (k', v') =>
      k.type.equal k'.type && k.synthPendingDepth == k'.synthPendingDepth &&
      k.localInsts.size == k'.localInsts.size &&
      (k.localInsts.zip k'.localInsts).all (fun (x, y) =>
        x.className == y.className && x.fvar.equal y.fvar) && exactResult v v')

private unsafe def mapTests : Bool := Id.run do
  let f := shiftName `test 0 16 16
  let closed := mkConst ``Nat
  let fv := mkFVar ⟨Name.num `test 1⟩
  let mv := mkMVar ⟨Name.num `test 2⟩
  let lm := mkSort (.mvar ⟨Name.num `test 3⟩)
  let outside := mkFVar ⟨Name.num `test 100⟩
  let exprs := #[closed, fv, mv, lm, outside,
    mkFVar ⟨Name.num `test 17⟩, -- collides with shifted fv
    mkLambda `named .implicit closed (mkApp fv (mkBVar 0))]
  let result (e : Expr) (mvars : Array Expr := #[]) : Option AbstractMVarsResult :=
    some { paramNames := #[`u], mvars, expr := e }
  let synthKey (e : Expr) (is : LocalInstances := #[]) : SynthInstanceCacheKey :=
    { type := e, localInsts := is, synthPendingDepth := 3 }
  let localInst (e : Expr) : LocalInstance := { className := `TestClass, fvar := e }
  -- Closed and out-of-range identifiers preserve entire maps, keys and values.
  for e in [closed, outside] do
    let c : Meta.Cache := {
      inferType := ({} : InferTypeCache).insert { expr := e, configKey := 7 } e,
      synthInstance := ({} : SynthInstanceCache).insert (synthKey e #[localInst e])
        (result e #[e]) }
    let r := (rmCache c f).run' {}
    unless ptrEq c.inferType.root r.inferType.root &&
        ptrEq c.synthInstance.root r.synthInstance.root do return false
    unless exactCaches r ((referenceRmCache c f).run' {}) do return false
  -- Only the key, only the value, only a local instance, only an abstract mvar,
  -- and only a universe mvar can require remapping. All payload positions are covered.
  let mut c : Meta.Cache := {}
  for e in exprs do
    for v in exprs do
      c := { c with inferType := c.inferType.insert { expr := e, configKey := 9 } v }
      c := { c with synthInstance := c.synthInstance.insert (synthKey e) (result v) }
      c := { c with
        synthInstance := c.synthInstance.insert (synthKey closed #[localInst e]) (result closed #[v]) }
      unless exactCaches ((rmCache c f).run' {}) ((referenceRmCache c f).run' {}) do return false
  -- Generic collision exercise checks original fold-order winners, including unchanged
  -- destination keys and cycles. Do not compare root order; compare exact final bindings.
  let mut m : PersistentHashMap Nat Nat := {}
  for n in [0:32] do m := m.insert n (100 + n)
  let unchanged := ((rmCacheMap m fun _ _ => pure none) id).run' {}
  unless ptrEq m.root unchanged.root do return false
  for divisor in [1:33] do
    for shift in [0:33] do
      let transform := fun (k v : Nat) => ((k + shift) % divisor, v + k)
      let expected := m.foldl (init := ({} : PersistentHashMap Nat Nat)) fun acc k v =>
        let (k', v') := transform k v
        acc.insert k' v'
      let actual := ((rmCacheMap m fun k v => do
        let (k', v') := transform k v
        return if k' == k && v' == v then none else some (k', v')) id).run' {}
      unless actual.toList.length == expected.toList.length &&
          expected.foldl (init := true) (fun ok k v => ok && actual.find? k == some v) do
        return false
  return true

run_meta do
  unless unsafe mapTests do throwError "section cache remap differs from frozen baseline"
