/-
Copyright (c) 2026 PaperLean contributors. Released under Apache 2.0.
-/
module
prelude
public import Lean.Meta.Basic
import Lean.Meta.AppBuilder
import all Lean.Environment
import Lean.PaperLean.ProofInputs
import Lean.PaperLean.Base

set_option genSizeOf false

namespace Lean.PaperLean.ProofConversion
open Lean Meta

private def head? : Nat → Expr → Option Expr
  | n+1, .app f _ => head? n f
  | 0, .app .. => none
  | _, e => some e

-- A direct theorem application whose result and expected type are applications of the same
-- predicate to two different definitions. The syntactic filter also avoids opening binders on
-- the usual tactic proofs, local hypotheses, and exact applications of the target predicate.
private def direct? (ty val : Expr) (fuel := 32) : Option (Name × Name × Name) := do
  match fuel, ty, val with
  | n+1, .forallE _ _ tb _, .lam _ _ vb _ => direct? tb vb n
  | _, .app f (.app g _), .app v _ =>
    let some (.const pred _) := head? 32 f | none
    let some (.const right _) := head? 32 g | none
    let some (.const proof _) := head? 32 v | none
    return (pred, right, proof)
  | _, _, _ => none

private def piBody : Nat → Expr → Expr
  | n+1, .forallE _ _ b _ => piBody n b
  | _, e => e

private structure Scan where
  fuel : Nat := 96
  reductions : Nat := 0
  -- The instantiated constant, including all universe levels.
  head? : Option Expr := none
  paths : Array (List Nat) := #[]
  exhausted : Bool := false

private structure Nodes where
  fuel : Nat
  seen : Std.HashSet Expr := {}
  names : NameSet := {}

-- Charge each distinct syntax node once, including atoms. The elaborated terms are DAGs.
private partial def visit (e : Expr) : StateM Nodes Bool := do
  let s ← get
  if s.seen.contains e then return true
  if s.fuel == 0 then return false
  set {s with fuel := s.fuel-1, seen := s.seen.insert e}
  match e with
  | .const n _ => modify fun s => {s with names := s.names.insert n}; return true
  | .app f a => if ← visit f then visit a else return false
  | .lam _ t b _ | .forallE _ t b _ => if ← visit t then visit b else return false
  | .letE _ t v b _ => if (← visit t) && (← visit v) then visit b else return false
  | .mdata _ a | .proj _ _ a => visit a
  | _ => return true

private def small (e : Expr) (limit : Nat) : Bool := (visit e).run' {fuel := limit}

-- Only the imported map of the current visibility is ready unconditionally. A generic
-- environment lookup can wait on a local declaration or realization after an import miss.
private def imported? (env : Environment) (n : Name) : Option ConstantInfo :=
  Environment.findImported? (env.base.get env) n

private def defn? (env : Environment) (n : Name) : Option DefinitionVal := do
  if env.isImportedConst n then
    let some (.defnInfo d) := imported? env n | none
    return d
  ProofInputs.lookup env n

private def deltaOnce? (e : Expr) : MetaM (Option Expr) := do
  let some (.const n us) := head? 24 e | return none
  let some d := defn? (← getEnv) n | return none
  if !small d.value 1024 then return none
  return some ((d.value.instantiateLevelParams d.levelParams us).beta e.getAppArgs)

-- Traverse only corresponding application spines, with fixed limits. If one step on the
-- right exposes the same abbreviation as on the left, compare its arguments without unfolding it.
private partial def align (l r : Expr) (depth : Nat) (revPath : List Nat) : StateRefT Scan MetaM (Expr × Expr) := do
  if depth == 0 || l == r || !l.isApp || !r.isApp then return (l,r)
  let s ← get
  if s.fuel == 0 then
    modify fun s => {s with exhausted := true}
    return (l,r)
  set { s with fuel := s.fuel-1 }
  let some f := head? 24 l | return (l,r)
  let some other := head? 24 r | return (l,r)
  if f != other then
    let .const ln _ := f | return (l,r)
    let .const rn _ := other | return (l,r)
    if s.reductions >= 12 || (s.head?.isSome && s.head? != some f) then return (l,r)
    let env ← getEnv
    if !env.isImportedConst ln || !env.isImportedConst rn then return (l,r)
    let some (.defnInfo ld) := imported? env ln | return (l,r)
    if !ld.hints.isAbbrev then return (l,r)
    modify fun s => {s with reductions := s.reductions+1}
    let some r' ← deltaOnce? r | return (l,r)
    if r'.getAppFn != f || r'.getAppNumArgs != l.getAppNumArgs || l == r' then return (l,r)
    modify fun s => {s with head? := some f, paths := s.paths.push revPath.reverse}
    return (l,r')
  if l.getAppNumArgs != r.getAppNumArgs || l.getAppNumArgs > 24 then return (l,r)
  let mut left := f
  let mut right := f
  for a in l.getAppArgs, b in r.getAppArgs, i in [:l.getAppNumArgs] do
    let (x,y) ← align a b (depth-1) (i :: revPath)
    left := mkApp left x
    right := mkApp right y
  return (left,right)

-- The scan retains at most twelve paths, each at most five levels deep. Rebuild only
-- those application spines, and require the same instantiated constant at every hit.
private def maskPath (head f : Expr) : List Nat → Expr → Option Expr
  | [], e => do
    guard (e.getAppFn == head && e.getAppNumArgs <= 24)
    return mkAppN f e.getAppArgs
  | i :: rest, e => do
    guard (e.getAppNumArgs <= 24)
    let args := e.getAppArgs
    let a ← args[i]?
    return mkAppN e.getAppFn (args.set! i (← maskPath head f rest a))

-- Only abstract syntax is needed. Registering local instances would inspect binder
-- types and could wait for the definition of an unfinished predecessor.
private def withProofBinders (value : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α :=
  go #[] value
where
  go (xs : Array Expr) : Expr → MetaM α
    | .lam n t b bi =>
      withLocalDeclNoLocalInstanceUpdate n bi (t.instantiateRev xs) fun x => go (xs.push x) b
    | e => k xs (e.instantiateRev xs)

private def build? (d : TheoremVal) (sig : ConstantInfo) : MetaM (Option Expr) := do
  withProofBinders d.value fun xs body => do
    let target := (piBody xs.size d.type).instantiateRev xs
    let .const _ us := body.getAppFn | return none
    let args := body.getAppArgs
    if args.size > 32 then return none
    let mut result := sig.instantiateTypeLevelParams us
    for _ in args do
      let .forallE _ _ b _ := result | return none
      result := b
    let inferred := result.instantiateRev args
    let .app p subject := inferred | return none
    let .app q expected := target | return none
    if p != q || subject == expected || subject.getAppFn == expected.getAppFn then return none
    let some src ← deltaOnce? subject | return none
    let some dst ← deltaOnce? expected | return none
    if !src.isApp || src.getAppFn != dst.getAppFn || src.getAppNumArgs != dst.getAppNumArgs then return none
    let ((src,dst),s) ← (align src dst 5 []).run {}
    let some head := s.head? | return none
    if s.exhausted || s.paths.size < 2 then return none
    let .const op us := head | return none
    let some opInfo := imported? (← getEnv) op | return none
    if !small opInfo.type 1024 then return none
    let dest := mkApp q dst
    let cert? ← withLocalDeclNoLocalInstanceUpdate `op .default (opInfo.instantiateTypeLevelParams us) fun f => do
      let some l := s.paths.foldlM (fun e path => maskPath head f path e) src | return none
      let some r := s.paths.foldlM (fun e path => maskPath head f path e) dst | return none
      let a := mkApp p l
      let b := mkApp q r
      let eq := mkApp3 (mkConst ``Eq [1]) (.sort 0) a b
      let refl := mkApp2 (mkConst ``Eq.refl [1]) (.sort 0) a
      let witness ← mkLambdaFVars #[f] (mkExpectedPropHint refl eq)
      return some (mkApp witness head)
    let some cert := cert? | return none
    return some (← mkLambdaFVars xs (mkApp4 (mkConst ``Eq.mp [0]) inferred dest cert body))

@[extern "lean_paperlean_trial_proofs"]
private opaque trialProofs (env : Kernel.Environment) (maxHeartbeats maxRecDepth : USize)
    (decls : @& Array Declaration) (cancelTk? : @& Option IO.CancelToken) :
    Except Kernel.Exception Kernel.Environment

private structure Closure where
  fuel : Nat := 8192
  pending : NameSet := {}
  done : NameSet := {}
  definitions : Array DefinitionVal := #[]

private def uses? (type value : Expr) : StateM Closure (Option NameSet) := do
  let (ok,nodes) := (do if ← visit type then visit value else return false).run
    {fuel := (← get).fuel}
  modify fun s => {s with fuel := nodes.fuel}
  return if ok then some nodes.names else none

-- Never inspect an asynchronous predecessor. Replay only the ordinary, eagerly published,
-- nonrecursive local definitions reachable from this proof. No premises are manufactured:
-- each local definition is checked by the real kernel in dependency order.
private partial def collect (env : Environment) (names : NameSet) :
    StateM Closure Bool := do
  for n in names do
    if env.isImportedConst n || (← get).done.contains n then continue
    let s ← get
    if s.pending.contains n || s.pending.size + s.definitions.size >= 8 then return false
    let some d := ProofInputs.lookup env n (privateKernel := true) | return false
    modify fun s => {s with pending := s.pending.insert n}
    let some deps ← uses? d.type d.value | return false
    unless ← collect env deps do return false
    modify fun s => {s with
      pending := s.pending.erase n
      done := s.done.insert n
      definitions := s.definitions.push d}
  return true

private def closure? (env : Environment) (d : TheoremVal) : Option (Array DefinitionVal) := do
  let (ok,s) := (do
    let some roots ← uses? d.type d.value | return false
    -- Unfolding an imported body can expose a sorry at this theorem for the first time.
    -- Keep the source proof (and its precise sorry diagnostics) in all such cases.
    if roots.contains ``sorryAx then return false
    collect env roots).run {}
  -- The root count and all local declaration inputs share one aggregate traversal budget.
  guard ok
  return s.definitions

private def candidate? (d : TheoremVal) (pred right proof : Name) : MetaM (Option TheoremVal) := do
  let env ← getEnv
  -- A module may export a theorem signature as an axiom. Inspect the type only.
  -- Avoid querying any pending local proof on the fast rejection path.
  if !env.isImportedConst proof || !env.isImportedConst pred then return none
  -- An inductive head cannot reduce to equality. Avoid wrappers around Eq/HEq/Iff
  -- whose proof shape may be consumed by dsimp and definitional-equality attributes.
  let some (.inductInfo _) := imported? env pred | return none
  let some info := imported? env proof | return none
  unless info matches .axiomInfo _ | .thmInfo _ do return none
  if !small info.type 4096 then return none
  let result := info.type.getForallBodyMaxDepth 32
  let .app f (.app g _) := result | return none
  let some f := head? 32 f | return none
  let some g := head? 32 g | return none
  if !f.isConstOf pred || g.isConstOf right then return none
  if d.type.hasMVar || d.value.hasMVar || d.type.hasFVar || d.value.hasFVar then return none
  let some value ← build? d info | return none
  let d' := { d with value }
  let opts ← getOptions
  let some definitions := closure? env d' | return none
  let normalLimit := Core.getMaxHeartbeats opts
  let normalDepth := maxRecDepth.get opts
  let depth := if normalDepth == 0 then 512 else min normalDepth 512
  let ctx ← readThe Core.Context
  Core.checkInterrupted
  let imported := env.base.private
  -- base.private holds imported constants. Reject custom bases with additional local
  -- declarations, so the replay cannot silently rely on any unaccounted local input.
  if !imported.constants.map₂.isEmpty then return none
  let batch := (definitions.map Declaration.defnDecl).push (.thmDecl d')
  -- One bounded genuine kernel trial for all local inputs and the proposed original type.
  -- The ordinary compiler still checks the selected theorem in its ordinary environment.
  let checked := trialProofs imported normalLimit.toUSize depth.toUSize batch ctx.cancelTk?
  match checked with
  | .ok _ =>
    return some d'
  | .error .interrupted => throwInterruptException
  | .error _ => return none

public def optimize (d : TheoremVal) : MetaM TheoremVal := do
  if !PaperLean.nativeAvailable d || !ProofInputs.enabled (← getOptions) then return d
  let start ← IO.getNumHeartbeats
  try
    let some (pred,right,proof) := direct? d.type d.value | return d
    -- The shape of equality proofs can affect downstream refl/defeq attributes.
    if pred == ``Eq || pred == ``HEq || pred == ``Iff || PaperLean.envRecording d then return d
    let core ← getThe Core.State
    let metaState ← getThe Meta.State
    try
      return (← candidate? d pred right proof).getD d
    catch e =>
      if e.isInterrupt then throw e
      return d
    finally
      modifyThe Meta.State fun _ => metaState
      modifyThe Core.State fun _ => core
  finally
    PaperLean.setHeartbeats start

end Lean.PaperLean.ProofConversion
