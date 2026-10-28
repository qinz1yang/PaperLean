/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lean.Meta.Basic
public import Lean.Meta.AbstractMVars
public import Lean.PaperLean.EnvDeps
public import Lean.PaperLean.Speculation
import Init.While
import Lean.Util.CollectFVars

public section

/-!
Typeclass results reused across the commands of a module (`Meta.synthInstanceCore?`), by `lean` on
the command line.

Lean caches typeclass results within a command (`Meta.Cache.synthInstance`) and solves the same
problems again in each later command, which in Mathlib is a large part of the time of theorem
headers. Here the result of Lean's search (`SynthInstance.main`) for a problem is kept with the
problem up to the renaming of free variables (the free variables that the problem and the local
instances reach, closed under their types and values, numbered in local-context order) and with
every access to the environment that the search made (`Lean.PaperLean.EnvDeps`). A later command
with the same problem, options and configuration takes that result, with its own free variables, if
every access gives the same answer in its environment; the rest of `synthInstanceCore?` (checking
and applying the result, Lean's own cache) runs as for a result that Lean's search found. Otherwise
the search runs as Lean's.

Only the main elaboration thread uses the cache, where commands are elaborated in order, and only
for problems without metavariables in them or in the context they reach; not with trace options or
diagnostics, nor under a custom unfolding predicate, a definitional-equality context, or the
tracking of unfolded let-variables (a side effect that a reuse would not repeat). With `PAPERLEAN_REUSE_ORACLE` set (for testing),
each reuse is compared with Lean's search, and `lean` runs again without reuse if they differ
(`Lean.PaperLean.Speculation`).
-/

namespace Lean.PaperLean.TCCache
open Meta

/-- A typeclass problem up to the renaming of free variables, which are replaced by `canonFVar`. -/
structure Key where
  type : Expr
  /-- The types and values of the free variables that the problem reaches, in local-context order. -/
  decls : Array (Expr × Option Expr)
  /-- The class and the number of each local instance. -/
  localInsts : Array (Name × Nat)
  synthPendingDepth : Nat
  maxResultSize : Nat
  configKey : UInt64
  univApprox : Bool
  opts : Options
  deriving BEq

instance : Hashable Key where
  hash k := k.decls.foldl (init := mixHash (hash k.type) (mixHash (hash k.configKey)
      (mixHash (hash k.synthPendingDepth) (hash k.maxResultSize))))
    fun h (t, v?) => mixHash h (mixHash (hash t) (hash v?))

/-- A result of Lean's search with what it depended on. -/
structure Entry where
  deps : EnvDeps.Deps
  /-- The result, with free variables replaced by `canonFVar`. -/
  result : Option AbstractMVarsResult
  /-- The number of macro scopes that the search took, by which a reuse advances the counter. -/
  macroScopes : Nat

private builtin_initialize entriesRef : IO.Ref (Std.HashMap Key (Array Entry)) ← IO.mkRef {}

/-- Reused, searched (cache missed), and searched because an entry's dependencies did not hold. -/
private builtin_initialize statsRef : IO.Ref (Nat × Nat × Nat) ← IO.mkRef (0, 0, 0)

/-- The numbers of typeclass problems of this process whose result was reused, searched, and
searched because an earlier search's dependencies did not hold. -/
def stats : BaseIO (Nat × Nat × Nat) := statsRef.get

private def maxEntriesPerKey := 4

/-- The `i`-th free variable of a problem, in `Key` and `Entry`. -/
private def canonFVar (i : Nat) : Expr :=
  .fvar ⟨.num `_paperlean_tc i⟩

/-- Whether this command may use the cache, under the options `opts`: on the command line, and not
with trace options or diagnostics, whose output reflects the search. -/
private def usableUnder (opts : Options) : Bool := Id.run do
  if !internal.cmdlineSnapshots.get opts || opts.getBool `diagnostics then
    return false
  for (n, v) in opts do
    if n.getRoot == `trace && n != `trace.profiler && v matches .ofBool true then
      return false
  return true

/-- The problem `type` with local instances `localInsts` as a `Key`, and the free variables in the
order of their numbers, unless the problem or the context it reaches has metavariables. -/
private def key? (localInsts : LocalInstances) (type : Expr) (maxResultSize : Nat) :
    MetaM (Option (Key × Array FVarId)) := do
  if type.hasMVar then
    return none
  let lctx ← getLCtx
  let mut todo : Array FVarId := (collectFVars {} type).fvarIds ++ localInsts.map (·.fvar.fvarId!)
  let mut reached : Array LocalDecl := #[]
  let mut seen : Std.HashSet FVarId := {}
  while h : todo.size > 0 do
    let id := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains id then continue
    seen := seen.insert id
    let some d := lctx.find? id | return none
    if d.type.hasMVar then return none
    todo := todo ++ (collectFVars {} d.type).fvarIds
    if let some v := d.value? then
      if v.hasMVar then return none
      todo := todo ++ (collectFVars {} v).fvarIds
    reached := reached.push d
  let decls := reached.qsort (·.index < ·.index)
  let mut num : Std.HashMap FVarId Nat := {}
  for h : i in [0:decls.size] do
    num := num.insert decls[i].fvarId i
  let canon (e : Expr) : Expr := e.replace fun
    | .fvar id => some (canonFVar (num.getD id 0))
    | _ => none
  let key : Key := {
    type := canon type
    decls := decls.map fun d => (canon d.type, d.value?.map canon)
    localInsts := localInsts.map fun li => (li.className, num.getD li.fvar.fvarId! 0)
    synthPendingDepth := (← read).synthPendingDepth
    maxResultSize
    configKey := (← getConfigWithKey).key
    univApprox := (← read).univApprox
    opts := ← getOptions }
  return some (key, decls.map (·.fvarId))

/-- `r` with the free variables `fvars` replaced by their numbers, unless it has other ones. -/
private def canonResult? (fvars : Array FVarId) (r : Option AbstractMVarsResult) :
    Option (Option AbstractMVarsResult) := do
  -- (a failed search is a result too)
  let some r := r | return none
  let mut num : Std.HashMap FVarId Nat := {}
  for h : i in [0:fvars.size] do
    num := num.insert fvars[i] i
  if (collectFVars {} r.expr).fvarIds.any (!num.contains ·) then
    failure
  return some { r with expr := r.expr.replace fun
    | .fvar id => some (canonFVar (num.getD id 0))
    | _ => none }

/-- `r` (from an `Entry`) with the free variables `fvars` put back. -/
private def restore (fvars : Array FVarId) (r : Option AbstractMVarsResult) :
    Option AbstractMVarsResult :=
  r.map fun r => { r with expr := r.expr.replace fun
    | .fvar ⟨.num p i⟩ => if p == `_paperlean_tc then fvars[i]?.map mkFVar else none
    | _ => none }

/-- Compares a reused result (as in `Entry`) with Lean's search, for `PAPERLEAN_REUSE_ORACLE`. -/
private def oracle (fvars : Array FVarId) (e : Entry)
    (search : MetaM (Option AbstractMVarsResult)) : MetaM Unit := do
  let reused := e.result
  let fresh? ← withoutModifyingState do
    let scope0 := (← getThe Core.State).nextMacroScope
    try
      let r ← search
      return some (r, (← getThe Core.State).nextMacroScope - scope0)
    catch _ => return none
  match fresh? with
  | some (fresh, scopes) =>
    if (canonResult? fvars fresh).map (·.map (·.expr)) != some (reused.map (·.expr)) ||
        scopes != e.macroScopes ||
        fresh.map (·.paramNames) != reused.map (·.paramNames) ||
        fresh.map (·.numMVars) != reused.map (·.numMVars) then
      Speculation.fail "typeclass cache: Lean's search gives another result"
  | none => Speculation.fail "typeclass cache: Lean's search fails"

/--
`search` (Lean's search for the problem `type` with local instances `localInsts`, of
`synthInstanceCore?`), or the result of the same search in an earlier command whose dependencies on
the environment hold.
-/
def withCache (localInsts : LocalInstances) (type : Expr) (maxResultSize : Nat)
    (search : MetaM (Option AbstractMVarsResult)) : MetaM (Option AbstractMVarsResult) := do
  let env ← getEnv
  -- (`nativeAvailable` first: the stage0 `lean` that builds stage1 has none of this module's state)
  let ctx ← read
  unless nativeAvailable env && env.asyncPrefix?.isNone && usableUnder (← getOptions) &&
      ctx.customCanUnfoldPredicate?.isNone && !ctx.trackZetaDelta && ctx.defEqCtx?.isNone do
    return (← search)
  let some (key, fvars) ← key? localInsts type maxResultSize | return (← search)
  let entries := (← entriesRef.get).getD key #[]
  let ns ← getCurrNamespace
  let openDecls ← getOpenDecls
  if let some e := entries.find? (·.deps.hold env ns openDecls) then
    statsRef.modify fun (r, n, f) => (r + 1, n, f)
    -- (a recording that this search is part of depends on what the reused search read)
    envRecordAll e.deps.accesses (unsafe unsafeCast e.deps.checks)
    modifyEnv e.deps.replay
    if (← IO.getEnv "PAPERLEAN_REUSE_ORACLE").isSome && (← Speculation.isEnabled) then
      oracle fvars e search
    modifyThe Core.State fun s => { s with nextMacroScope := s.nextMacroScope + e.macroScopes }
    return restore fvars e.result
  statsRef.modify fun (r, n, f) => (r, n + 1, if entries.isEmpty then f else f + 1)
  let scope0 := (← getThe Core.State).nextMacroScope
  let rec_ ← EnvDeps.start
  let r ← tryFinally search (discard rec_.stop)
  if let .ok deps ← rec_.stop then
    if let some result := canonResult? fvars r then
      let macroScopes := (← getThe Core.State).nextMacroScope - scope0
      entriesRef.modify fun m =>
        m.insert key ((#[({ deps, result, macroScopes } : Entry)] ++ entries).take maxEntriesPerKey)
  return r

end Lean.PaperLean.TCCache
