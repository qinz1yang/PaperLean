module
public import Lean
import all Lean.Meta.WHNF
open Lean Meta
universe u v
structure Wide (α : Type u) (β : Type v) where
  selected : α
  other : β
  dependent : selected = selected
  named : β → β
  unused0 : (α → β) → α → β
  unused1 : (α → β) → α → β
  unused2 : (α → β) → α → β
  unused3 : (α → β) → α → β
  unused4 : (α → β) → α → β
  unused5 : (α → β) → α → β
  unused6 : (α → β) → α → β
  unused7 : (α → β) → α → β
  unused8 : (α → β) → α → β
  unused9 : (α → β) → α → β
  unused10 : (α → β) → α → β
  unused11 : (α → β) → α → β
  unused12 : (α → β) → α → β
  unused13 : (α → β) → α → β
  unused14 : (α → β) → α → β
  unused15 : (α → β) → α → β
  unused16 : (α → β) → α → β
  unused17 : (α → β) → α → β
  unused18 : (α → β) → α → β
  unused19 : (α → β) → α → β
  unused20 : (α → β) → α → β
  unused21 : (α → β) → α → β
  unused22 : (α → β) → α → β
  unused23 : (α → β) → α → β
  unused24 : (α → β) → α → β
  unused25 : (α → β) → α → β
  unused26 : (α → β) → α → β
  unused27 : (α → β) → α → β
  unused28 : (α → β) → α → β
  unused29 : (α → β) → α → β
  unused30 : (α → β) → α → β
  unused31 : (α → β) → α → β
def wide (α : Type u) (β : Type v) (x : α) (y : β) : Wide α β where
  selected := x
  other := y
  dependent := rfl
  named := fun named => named
  unused0 := fun f z => f z
  unused1 := fun f z => f z
  unused2 := fun f z => f z
  unused3 := fun f z => f z
  unused4 := fun f z => f z
  unused5 := fun f z => f z
  unused6 := fun f z => f z
  unused7 := fun f z => f z
  unused8 := fun f z => f z
  unused9 := fun f z => f z
  unused10 := fun f z => f z
  unused11 := fun f z => f z
  unused12 := fun f z => f z
  unused13 := fun f z => f z
  unused14 := fun f z => f z
  unused15 := fun f z => f z
  unused16 := fun f z => f z
  unused17 := fun f z => f z
  unused18 := fun f z => f z
  unused19 := fun f z => f z
  unused20 := fun f z => f z
  unused21 := fun f z => f z
  unused22 := fun f z => f z
  unused23 := fun f z => f z
  unused24 := fun f z => f z
  unused25 := fun f z => f z
  unused26 := fun f z => f z
  unused27 := fun f z => f z
  unused28 := fun f z => f z
  unused29 := fun f z => f z
  unused30 := fun f z => f z
  unused31 := fun f z => f z

private def sameOptionExpr (a b : Option Expr) : Bool := match a, b with
  | some a, some b => a.equal b
  | none, none => true
  | _, _ => false

private def checkField (info : ConstantInfo) (us : List Level) (args : Array Expr)
    (i : Nat) : MetaM Unit := do
  let e := mkAppN (mkConst info.name us) args
  -- Cold, matching hot, and other-universe memo states. A cold/other-level fast path
  -- may omit the full memo; later full instantiation must compute the baseline bytes.
  for memoKind in [0:3] do
    modifyThe Core.State fun s => { s with cache.instLevelValue := s.cache.instLevelValue.erase info.name }
    let expected := info.instantiateValueLevelParams! us
    if memoKind == 1 then discard <| instantiateValueLevelParams info us
    if memoKind == 2 then
      discard <| instantiateValueLevelParams info (us.map Level.succ)
    let before ← getThe Core.State
    let metaBefore ← get
    let fast ← unfoldDefaultProj? info us e i
    let coreAfter ← getThe Core.State
    let metaAfter ← get
    unless before.ngen.namePrefix == coreAfter.ngen.namePrefix && before.ngen.idx == coreAfter.ngen.idx do
      throwError "projection changed name generation"
    unless (unsafe ptrEq metaBefore.cache metaAfter.cache) do
      throwError "projection changed Meta caches"
    if memoKind == 1 then
      let some (_, old) := before.cache.instLevelValue.find? info.name | throwError "missing hot fixture"
      let some (_, now) := coreAfter.cache.instLevelValue.find? info.name | throwError "lost hot memo"
      unless (unsafe ptrEq old now) do throwError "existing full-value hit was replaced"
    let some fast := fast | throwError "fully applied fixture rejected"
    match fast with
    | .inr field =>
      let expectedField ← projectCore? (expected.betaRev args.reverse) i
      unless expectedField.any (·.equal field) do throwError "selected field differs"
      unless projOracle || memoKind == 1 do
        let old := before.cache.instLevelValue.find? info.name
        let now := coreAfter.cache.instLevelValue.find? info.name
        let same := match old, now with
          | none, none => true
          | some (u, a), some (v, b) => u == v && (unsafe ptrEq a b)
          | _, _ => false
        unless same do throwError "fast miss unexpectedly changed full-value memo"
    | .inl value =>
      unless sameOptionExpr value (PaperLean.betaRev expected args.reverse) do
        throwError "fallback beta result differs"
    let actual ← instantiateValueLevelParams info us
    unless actual.equal expected do throwError "later full instantiation differs from baseline"
    let again ← instantiateValueLevelParams info us
    unless (unsafe ptrEq actual again) do throwError "full instantiation cache hit was lost"

run_meta do
  let info ← getConstInfo ``wide
  let tagged := match info with
    | .defnInfo d =>
      let value := d.value.replace fun e =>
        if e.isBVar then some (.mdata {} e) else none
      ConstantInfo.defnInfo { d with value := .mdata {} value }
    | _ => info
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  for us in [[Level.zero, Level.zero], [Level.param `u, Level.param `v], [u, v]] do
    let type := info.type.instantiateLevelParams info.levelParams us
    forallTelescope type fun xs _ => do
      let ms ← xs.mapM fun x => do mkFreshExprMVar (← inferType x)
      for args in [xs, ms] do
        for transparency in [TransparencyMode.default, .instances, .reducible] do
          withTransparency transparency do
            for i in [0:36] do checkField info us args i
            for i in [0:4] do checkField tagged us args i
      -- Partial and over applications remain on the original path.
      let partialApp := mkAppN (mkConst ``wide us) (xs.extract 0 (xs.size - 1))
      unless (← unfoldDefaultProj? info us partialApp 0).isNone do
        throwError "partial application incorrectly projected"
      let overApp := mkApp (mkAppN (mkConst ``wide us) xs) (mkNatLit 0)
      unless (← unfoldDefaultProj? info us overApp 0).isNone do
        throwError "over application incorrectly projected"
      -- The custom-predicate branch permits a closed selected field too.
      withReader (fun c => { c with customCanUnfoldPredicate? := some (fun _ _ => pure true) }) do
        checkField info us xs 3
