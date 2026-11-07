module
public import Lean
import all Lean.Meta.Basic
import all Lean.PaperLean.TCCache
open Lean Meta PaperLean.TCCache

-- Frozen 9854b799 forward implementation, without semantic edits.
private unsafe def referenceWithInsertAt (env : Environment) (ops : Array CacheOp) : Array CacheOp :=
    Id.run do
  let mut out := ops
  for h : i in [0:ops.size] do
    let .pureLookup c k none _ := ops[i] | continue
    let mut j := i + 1
    while h' : j < ops.size do
      match ops[j] with
      | .insert c' k' _ =>
        if c' == c && sameKey c k' k then
          out := out.set! i (.pureLookup c k none (some j))
          break
        unless pureKey env c' k' do break
      | .pureLookup c' k' .. => if c' == c && sameKey c k' k then break
      | .lookup .. => break
      j := j + 1
  return out


private unsafe def opKey (c : UInt8) (e : Expr) (salt : Nat := 0) : NonScalar :=
  if c == 0 || c == 3 then unsafeCast ({ expr := e, configKey := salt.toUInt64 } : ExprConfigCacheKey)
  else if c == 1 then unsafeCast ({
    expr := e, configKey := salt.toUInt64,
    nargs? := if salt == 0 then none else some salt } : InfoCacheKey)
  else unsafeCast ({ type := e, localInsts := #[], synthPendingDepth := salt } : SynthInstanceCacheKey)

private unsafe def sameOp : CacheOp → CacheOp → Bool
  | .lookup c k v, .lookup c' k' v' => c == c' && ptrEq k k' && sameObj? v v'
  | .insert c k v, .insert c' k' v' => c == c' && ptrEq k k' && ptrEq v v'
  | .pureLookup c k v j, .pureLookup c' k' v' j' =>
    c == c' && ptrEq k k' && sameObj? v v' && j == j'
  | _, _ => false

private unsafe def checkTrace (env : Environment) (ops : Array CacheOp) : Bool :=
  let a := referenceWithInsertAt env ops
  let b := withInsertAt env ops
  a.size == b.size && (a.zip b).all fun (x, y) => sameOp x y

private unsafe def traces (env : Environment) : Bool := Id.run do
  let e := mkConst ``Nat
  let k := opKey 1 e
  let kOtherConfig := opKey 1 e 7 -- sameKey intentionally ignores config/nargs
  let other := opKey 1 (mkConst ``Bool)
  let impure := opKey 3 e
  let v : NonScalar := unsafeCast e
  let palette : Array CacheOp := #[
    .pureLookup 1 k none none, .pureLookup 1 kOtherConfig (some v) none,
    .pureLookup 1 other none (some 99), .insert 1 kOtherConfig v,
    .insert 1 other v, .lookup 1 other none, .insert 3 impure v]
  -- Exhaust all short traces: same-key lookups, ordinary barriers, impure insertions,
  -- duplicate writes and pre-existing annotations on unmatched lookups.
  for len in [0:5] do
    for encoded in [0:palette.size ^ len] do
      let mut code := encoded
      let mut ops := #[]
      for _ in [0:len] do
        let some op := palette[code % palette.size]? | return false
        ops := ops.push op
        code := code / palette.size
      unless checkTrace env ops do return false
  -- Matching an impure insertion takes precedence over the impurity barrier.
  unless checkTrace env #[.pureLookup 3 impure none none, .insert 3 impure v] do return false
  let lamX := mkLambda `x .default e (mkBVar 0)
  let lamY := mkLambda `y .default e (mkBVar 0)
  let lamI := mkLambda `x .implicit e (mkBVar 0)
  let mut rich := palette
  for c in [0, 1, 2, 3] do
    for e in [lamX, lamY, lamI, mkConst ``List [.zero], mkApp (mkConst ``List [.zero]) e] do
      let k := opKey c e
      rich := rich.push (.pureLookup c k none none) |>.push (.insert c k v)
  let mut seed := 17
  for _ in [0:1024] do
    let mut ops := #[]
    for _ in [0:48] do
      seed := (seed * 1664525 + 1013904223) % 4294967296
      let some op := rich[seed % rich.size]? | return false
      ops := ops.push op
    unless checkTrace env ops do return false
  -- Nested distinct pure misses: the baseline repeatedly walks the same suffix.
  for n in [32, 64, 128, 256] do
    let keys := (List.range n).toArray.map fun i =>
      opKey 1 (mkConst ``List [Level.ofNat i])
    let ops := keys.map (fun k => CacheOp.pureLookup 1 k none none) ++
      keys.reverse.map (fun k => CacheOp.insert 1 k v)
    unless checkTrace env ops do return false
  return true

run_meta do
  unless unsafe traces (← getEnv) do throwError "withInsertAt differs from frozen baseline"
