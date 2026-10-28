/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lean.Elab.Term.TermElabM
public import Lean.PaperLean.EnvDeps
public import Lean.PaperLean.Speculation

public section

/-!
Reuse of a scope's elaborated section variables (`Lean.Elab.Command.runTermElabM`), by `lean` on the
command line.

Lean elaborates the binders of all `variable`s of the current scope again for every command that
uses them, which in Mathlib is a large part of the time of some modules. Here the variables that
this elaboration gave for an earlier command of the scope, as a closed telescope, and its universe
names are used again when that elaboration would give the same now: the binders, the variables'
unique names, the options, the universe names and the visibility (`Environment.isExporting`) are
the same, and every access to the environment that the earlier elaboration made gives the same
answer in the current environment, namespace and open declarations (`Lean.PaperLean.EnvDeps`); its
changes to the environment, records of module uses, are repeated, and the counter of macro scopes
advances as the elaboration advanced it. The telescope is introduced with
fresh free variables, as `runTermElabM` itself does when it rebuilds the local context. Otherwise
the binders are elaborated as Lean does. A reused elaboration differs from Lean's in the variables'
types having their metavariables instantiated, in the macro scopes of inaccessible binder names,
which come from the earlier command, and in the info trees, which have no nodes for the binders.

With trace options or diagnostics on, whose output reflects the elaboration, the binders are always
elaborated. With `PAPERLEAN_REUSE_ORACLE` set (for testing), each reuse is also checked in the
background by elaborating the binders as Lean does and comparing; if one differs, `lean` runs again
without reuse (`Lean.PaperLean.Speculation`).
-/

namespace Lean.PaperLean.SectionVars
open Elab Term Meta

/-- The section variables as elaborated for a command, with what that elaboration depended on. -/
structure Entry where
  varDecls : Array Syntax
  varUIds : Array Name
  opts : Options
  levelNames : List Name
  isExporting : Bool
  deps : EnvDeps.Deps
  /-- `∀ xs, Prop` with the metavariables instantiated: the variables, introduced again with fresh
  free variables on reuse (as `runTermElabM` itself does when it rebuilds the local context). -/
  ctxType : Expr
  numVars : Nat
  /-- The position in `xs` of the variable of each of `varUIds`. -/
  uidIdxs : Array Nat
  levelNamesAfter : List Name
  /-- The number of macro scopes that the elaboration took: a reuse advances the counter by as many,
  so that the names with macro scopes made later in the command (e.g. of an anonymous instance) are
  those of Lean's elaboration. -/
  macroScopes : Nat
  /-- Where it was elaborated, for debugging. -/
  pos : String

private builtin_initialize entriesRef : IO.Ref (Array Entry) ← IO.mkRef #[]

/-- The binders (`varDecls`, `varUIds`) whose elaboration could not be recorded (it ran a tactic or,
with `PAPERLEAN_REUSE_USER_ELABS=0`, a user elaborator): they are not recorded again, as their
elaboration does the same. -/
private builtin_initialize unrecordableRef : IO.Ref (Array (Array Syntax × Array Name)) ←
  IO.mkRef #[]

private def maxEntries := 8

/-- Reused, elaborated, and elaborated because the dependencies of an entry did not hold. -/
private builtin_initialize statsRef : IO.Ref (Nat × Nat × Nat) ← IO.mkRef (0, 0, 0)

/-- The numbers of commands of this process whose section variables were reused, elaborated, and
elaborated because an earlier elaboration's dependencies did not hold. -/
def stats : BaseIO (Nat × Nat × Nat) := statsRef.get

/-- Whether section variables may be reused under the options `opts`: on the command line, and not
with trace options or diagnostics, whose output reflects the elaboration. -/
private def reusableUnder (opts : Options) : Bool := Id.run do
  if !internal.cmdlineSnapshots.get opts || opts.getBool `diagnostics then
    return false
  for (n, v) in opts do
    if n.getRoot == `trace && n != `trace.profiler && v matches .ofBool true then
      return false
  return true

/-! The oracle (`PAPERLEAN_REUSE_ORACLE`). -/

/-- Whether names are equal, or both inaccessible (with macro scopes) and equal without them. -/
private def sameName (a b : Name) : Bool :=
  a == b || (a.hasMacroScopes && b.hasMacroScopes && a.eraseMacroScopes == b.eraseMacroScopes)

private unsafe def sameExprImpl (a b : Expr) : Bool :=
  (go a b |>.run' {}).run
where
  go (a b : Expr) : StateT (Std.HashSet (USize × USize)) Id Bool := do
    if ptrEq a b then
      return true
    let key := (ptrAddrUnsafe a, ptrAddrUnsafe b)
    if (← get).contains key then
      return true
    let r ← match a, b with
      | .bvar i, .bvar j => pure (i == j)
      | .fvar x, .fvar y => pure (x == y)
      | .mvar x, .mvar y => pure (x == y)
      | .sort u, .sort v => pure (u == v)
      | .const n us, .const m vs => pure (n == m && us == vs)
      | .app f x, .app g y => go f g <&&> go x y
      | .lam n t c bi, .lam m s d bj | .forallE n t c bi, .forallE m s d bj =>
        pure (sameName n m && bi == bj) <&&> go t s <&&> go c d
      | .letE n t v c nd, .letE m s w d nd' =>
        pure (sameName n m && nd == nd') <&&> go t s <&&> go v w <&&> go c d
      | .lit l, .lit l' => pure (l == l')
      | .mdata d e, .mdata d' e' => pure (d == d') <&&> go e e'
      | .proj s i e, .proj s' i' e' => pure (s == s' && i == i') <&&> go e e'
      | _, _ => pure false
    if r then
      modify (·.insert key)
    return r

/-- Structural equality of expressions with equal binder kinds and names compared by `sameName`. -/
@[implemented_by sameExprImpl]
private opaque sameExpr (a b : Expr) : Bool

/-- `∀ xs, Prop` with the metavariables instantiated, and the positions of the variables of
`varUIds` in `xs`, if `xs` are free variables and the result has no metavariables; computed without
changing the state. -/
private def summarize (xs : Array Expr) (sectionFVars : NameMap Expr) (varUIds : Array Name) :
    TermElabM (Option (Expr × Array Nat)) := do
  unless xs.all (·.isFVar) do
    return none
  let ctxType ← withoutModifyingState do instantiateMVars (← mkForallFVars xs (mkSort .zero))
  if ctxType.hasMVar || ctxType.hasFVar then
    return none
  return some (ctxType, varUIds.filterMap fun uid => (sectionFVars.find? uid).bind xs.idxOf?)

/-- Elaborates the section variables as Lean does in a background task, in this command's state,
and compares the result with the reused entry `e`. -/
private def oracle (e : Entry)
    (elabVars : ∀ {β}, (Array Expr → NameMap Expr → TermElabM β) → TermElabM β) :
    TermElabM Unit := do
  let ctx ← read
  let st ← get
  let metaCtx ← readThe Meta.Context
  let metaSt ← getThe Meta.State
  let run ← Core.wrapAsync (cancelTk? := none) fun (_ : Unit) => do
    let act : TermElabM Unit := do
      try
        let scope0 := (← getThe Core.State).nextMacroScope
        let fresh? ← elabVars fun xs sectionFVars => do
          let s? ← summarize xs sectionFVars e.varUIds
          let levelNames ← getLevelNames
          let scopes := (← getThe Core.State).nextMacroScope - scope0
          return s?.map fun s => (s, xs.size, levelNames, scopes)
        match fresh? with
        | some ((ctxType, uidIdxs), n, levelNames, scopes) =>
          unless n == e.numVars && uidIdxs == e.uidIdxs && levelNames == e.levelNamesAfter &&
              scopes == e.macroScopes && sameExpr e.ctxType ctxType do
            Speculation.fail "section variables: elaborated differently"
        | _ => Speculation.fail "section variables: cannot be compared"
      catch _ =>
        Speculation.fail "section variables: their elaboration fails"
    act.run ctx st |>.run' metaCtx metaSt
  Speculation.addCheck (← BaseIO.asTask (discard <| (run ()).toBaseIO))

/--
Elaborates the section variables with `elabVars` (Lean's elaboration in `runTermElabM`, which passes
the variables and the map from their unique names to them to its continuation) and continues with
`k`, or reuses an earlier elaboration of the same section variables whose dependencies hold.
-/
def withSectionVars (varDecls : Array Syntax) (varUIds : Array Name) (opts : Options)
    (elabVars : ∀ {β}, (Array Expr → NameMap Expr → TermElabM β) → TermElabM β)
    (k : Array Expr → NameMap Expr → TermElabM α) : TermElabM α := do
  if varDecls.isEmpty || !reusableUnder opts || !(← getLCtx).isEmpty ||
      !(← getMCtx).decls.isEmpty then
    return (← elabVars k)
  let levelNames ← getLevelNames
  let env ← getEnv
  let ns ← getCurrNamespace
  let openDecls ← getOpenDecls
  let entries ← entriesRef.get
  let candidates := entries.filter fun (e : Entry) =>
    e.varUIds == varUIds && e.levelNames == levelNames && e.isExporting == env.isExporting &&
    e.opts == opts && e.varDecls == varDecls
  let debug := (← IO.getEnv "PAPERLEAN_DEBUG_REUSE").isSome
  let fileMap ← getFileMap
  let pos := s!"{(← getRef).getPos?.map fun p => fileMap.toPosition p}"
  if let some e := candidates.find? (·.deps.hold env ns openDecls) then
    if debug then
      IO.eprintln s!"PaperLean: {pos}: section variables of {e.pos} reused \
        ({e.deps.checks.size} checks, {e.deps.replays.size} replays)"
    statsRef.modify fun (r, n, f) => (r + 1, n, f)
    if (← IO.getEnv "PAPERLEAN_REUSE_ORACLE").isSome && (← Speculation.isEnabled) then
      oracle e elabVars
    modifyEnv e.deps.replay
    setLevelNames e.levelNamesAfter
    modifyThe Core.State fun s => { s with nextMacroScope := s.nextMacroScope + e.macroScopes }
    return (← withLCtx {} {} <| forallBoundedTelescope e.ctxType e.numVars fun xs _ => do
      let mut sectionFVars := {}
      for uid in varUIds, i in e.uidIdxs do
        sectionFVars := sectionFVars.insert uid xs[i]!
      k xs sectionFVars)
  if debug then
    for e in candidates do
      if let some a := e.deps.firstFailure? env ns openDecls then
        IO.eprintln s!"PaperLean: {pos}: section variables of {e.pos} not reused: \
          {EnvDeps.describe env a}"
  statsRef.modify fun (r, n, f) => (r, n + 1, if candidates.isEmpty then f else f + 1)
  if (← unrecordableRef.get).any fun (d, u) => u == varUIds && d == varDecls then
    return (← elabVars k)
  let scope0 := (← getThe Core.State).nextMacroScope
  let rec_ ← EnvDeps.start
  tryFinally
    (elabVars fun xs sectionFVars => do
      let deps? ← rec_.stop
      if let .error why := deps? then
        if debug then
          IO.eprintln s!"PaperLean: {pos}: section variables not recordable: {why}"
        unrecordableRef.modify fun us => (#[(varDecls, varUIds)] ++ us).take maxEntries
      if let .ok deps := deps? then
        if let some (ctxType, uidIdxs) ← summarize xs sectionFVars varUIds then
          let e : Entry := {
            varDecls, varUIds, opts, levelNames, isExporting := env.isExporting, deps, ctxType
            numVars := xs.size, uidIdxs, levelNamesAfter := ← getLevelNames
            macroScopes := (← getThe Core.State).nextMacroScope - scope0, pos }
          -- (entries for the same binders are kept too: their dependencies may hold at other times,
          -- e.g. in another namespace)
          entriesRef.modify fun es => (#[e] ++ es).take maxEntries
      k xs sectionFVars)
    (discard rec_.stop)

end Lean.PaperLean.SectionVars
