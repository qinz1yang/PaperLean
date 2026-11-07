/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lean.Elab.Term.TermElabM
public import Lean.PaperLean.EnvDeps
public import Lean.PaperLean.Speculation
import Lean.PaperLean.TCCache
import Std.Data.HashMap.Basic
import all Lean.Meta.Basic
import all Lean.ExtraModUses

-- (no `SizeOf` instances for PaperLean's types: an instance of a module of `Lean` would be one of
-- every environment that imports it, which Lean's searches would try)
set_option genSizeOf false
set_option genInjectivity false

public section

/-!
Reuse of a scope's elaborated section variables (`Lean.Elab.Command.runTermElabM`), by `lean` on the
command line when a `paperlean` command asks for it (`Speculation.reuse`), on the threads that
elaborate commands in order (`Speculation.onElabThread`).

Lean elaborates the binders of all `variable`s of the current scope again for every command that
uses them, which in Mathlib is a large part of the time of some modules. Each command elaborates
them from the same state (empty local and metavariable contexts, empty caches, ...), and what the
elaboration gives is the state at its end: the variables in the local context, the metavariable
context, Lean's caches, the info trees, the counters of names and macro scopes. Here the state that
an earlier command's elaboration ended with is set again, and the command goes on from it as from
Lean's elaboration, when that elaboration would give the same now: the binders, the variables'
unique names, the options, the universe names, the visibility (`Environment.isExporting`), the kind
of section (noncomputable, meta), whether info trees are enabled and the counters of macro scopes at
the start are the same, the
recursion depth is at most the earlier one, every access to the environment that the elaboration
made gives the same answer in the current environment, namespace and open declarations
(`Lean.PaperLean.EnvDeps`), and the module uses that it looked for are there, as it changed nothing
(`hasModuleUses`).

Lean's elaboration uses the names that it makes only as names, so the state that it would end with
now differs from the earlier one only in these names: the identifiers of the free variables and
metavariables, and the names with macro scopes, made in each command's own quotation context. The
reuse renumbers the identifiers to those that Lean's elaboration gives from the current index of the
generator (`remapped`), advances the generator by as many names as the elaboration took, so that the
later names are Lean's, and renames the quotation context of the names with macro scopes to the current
one in the expressions of the state (the variables' names and types, the metavariables' types and
values, Lean's caches), so that the declarations are Lean's; the syntax in the info trees and in the
data for error messages keeps the earlier names. The reuse's own work counts no heartbeats.

The numbers must be Lean's: they decide the order of the maps and sets of identifiers that tactics keep,
which shows in the proofs (`aesop` picks hypotheses for its forward rules so, and binder names in its
proofs differ), and Verso docstrings store them (`Doc.Data.Local`).

Macros use the names with macro scopes only as names (`scanExpr` finds them elsewhere in the result).
A macro that prints such a name into a string reads the numbering of macro scopes, Lean's internal
state, and is outside what PaperLean guarantees: the string may hold another hash of the quotation
context than in Lean, with the term that it is in.
An elaboration is not kept if it runs a tactic or an elaborator that is not Lean's own and not on the
whitelist (`Lean.PaperLean.EnvDeps`, `Lean.PaperLean.Whitelist`), if it changes the environment, leaves unsolved elaboration problems but typeclass problems, unassigned or
delayed-assigned metavariables or metavariables among the variables (auto-bound), or has names of
its quotation context where a reuse does not rename them (in constants, universe names, metadata,
string literals: e.g. the labels of `sorry`), and with trace options or diagnostics on (whose
output reflects the elaboration). With `PAPERLEAN_REUSE_ORACLE` set (for testing), each reuse is
compared with Lean's elaboration from the same state; `lean` fails if they differ
(`Lean.PaperLean.Speculation`).
-/

namespace Lean.PaperLean.SectionVars
open Elab Term Meta

builtin_initialize
  EnvDeps.moduleUseExtsRef.set
    #[extraModUses.toEnvExtension.idx, indirectModUseExt.toEnvExtension.idx]

/-- The entries of the extensions of module uses (`Lean.ExtraModUses`) of `env`'s module, the
newest first, read unrecorded. -/
def moduleUses (env : Environment) : List ExtraModUse × List IndirectModUse :=
  envWithoutRecording fun _ =>
    (extraModUses.getEntries (asyncMode := .local) env,
      indirectModUseExt.getEntries (asyncMode := .mainOnly) env)

private unsafe def isSuffixImpl {α : Type} (l s : List α) : Bool :=
  match l with
  | [] => ptrAddrUnsafe l == ptrAddrUnsafe s
  | _ :: t => ptrAddrUnsafe l == ptrAddrUnsafe s || isSuffixImpl t s

/-- Whether `s` is a suffix of `l` (the same list cells). -/
@[implemented_by isSuffixImpl]
private opaque isSuffix {α : Type} (l s : List α) : Bool

/-- Whether `env` has the module uses `uses` (of `moduleUses`), as it has if it has only added
some since. A computation that recorded the module uses that it needed and found them all
(changing nothing) finds them all in `env` too. -/
def hasModuleUses (env : Environment) (uses : List ExtraModUse × List IndirectModUse) : Bool :=
  let (extra, indirect) := moduleUses env
  (isSuffix extra uses.1 || uses.1.all fun e =>
      envWithoutRecording fun _ => (extraModUses.getState (asyncMode := .local) env).contains e) &&
    (isSuffix indirect uses.2 || uses.2.all indirect.contains)

/-! The names of a quotation context, and their renaming. -/

/-- The components of `n`, each a name of one component. -/
private def comps (n : Name) : Array Name :=
  n.components.toArray

/-- The name of the components `cs`. -/
private def ofComps (cs : Array Name) : Name :=
  cs.foldl (init := .anonymous) fun n c => match c with
    | .str _ s => .str n s
    | .num _ i => .num n i
    | .anonymous => n

/-- Whether the components `cs` hold `ctx` at position `i`. -/
private def holdsAt (cs ctx : Array Name) (i : Nat) : Bool :=
  i + ctx.size ≤ cs.size && (List.range ctx.size).all fun j => cs[i + j]! == ctx[j]!

/-- Whether the name `n` has macro scopes of the quotation context with the components `ctx`. -/
private def ofCtx (ctx : Array Name) (n : Name) : Bool :=
  n.hasMacroScopes &&
    let cs := comps n
    (List.range cs.size).any (holdsAt cs ctx)

/-- `n` with the quotation context with the components `a` replaced by the one with `b`. -/
private def renameName (a b : Array Name) (n : Name) : Name := Id.run do
  if !n.hasMacroScopes then
    return n
  let cs := comps n
  let mut out := #[]
  let mut i := 0
  let mut changed := false
  while i < cs.size do
    if holdsAt cs a i then
      out := out ++ b
      i := i + a.size
      changed := true
    else
      out := out.push cs[i]!
      i := i + 1
  return if changed then ofComps out else n

private partial def levelOfCtx (isCtx : Name → Bool) : Level → Bool
  | .param n => isCtx n
  | .succ u => levelOfCtx isCtx u
  | .max u v | .imax u v => levelOfCtx isCtx u || levelOfCtx isCtx v
  | _ => false

/-- What `e` holds of the names of a quotation context (`isCtx`): none (`0`), names that a reuse
renames, binder names and names in metadata (`1`), or others (`2`): in constants, universe names,
metadata keys or syntax, or a string literal of a name's macro scopes (a name as data). -/
private unsafe def scanExpr (isCtx : Name → Bool) (e : Expr) :
    StateM (Std.HashMap USize UInt8) UInt8 := do
  if let some r := (← get)[ptrAddrUnsafe e]? then
    return r
  let ofName (n : Name) : UInt8 := if isCtx n then 1 else 0
  let r ← match e with
    | .const n us => pure (if isCtx n || us.any (levelOfCtx isCtx) then 2 else 0)
    | .sort u => pure (if levelOfCtx isCtx u then 2 else 0)
    | .lit (.strVal s) => pure (if s == "_hyg" || s == "_hygCtx" || s == "_@" then 2 else 0)
    | .app f a => pure (max (← scanExpr isCtx f) (← scanExpr isCtx a))
    | .lam n t b _ | .forallE n t b _ =>
      pure (max (ofName n) (max (← scanExpr isCtx t) (← scanExpr isCtx b)))
    | .letE n t v b _ =>
      let s ← scanExpr isCtx t
      pure (max (ofName n) (max s (max (← scanExpr isCtx v) (← scanExpr isCtx b))))
    | .mdata d b =>
      let m := d.entries.foldl (init := (0 : UInt8)) fun m (k, v) => max m <|
        if isCtx k then 2 else match v with
          | .ofName n => ofName n
          | .ofSyntax _ => 2
          | _ => 0
      pure (max m (← scanExpr isCtx b))
    | .proj s _ b => pure (max (if isCtx s then 2 else 0) (← scanExpr isCtx b))
    | _ => pure 0
  modify (·.insert (ptrAddrUnsafe e) r)
  return r

/-- `e` with its binder names and the names in its metadata renamed by `f`; the same object where
nothing is renamed. -/
private unsafe def renameExpr (f : Name → Name) (e : Expr) :
    StateM (Std.HashMap USize Expr) Expr := do
  if let some r := (← get)[ptrAddrUnsafe e]? then
    return r
  let r ← match e with
    | .app g a => pure (e.updateApp! (← renameExpr f g) (← renameExpr f a))
    | .lam n t b bi =>
      let t' ← renameExpr f t
      let b' ← renameExpr f b
      let n' := f n
      pure (if n' == n then e.updateLambdaE! t' b' else .lam n' t' b' bi)
    | .forallE n t b bi =>
      let t' ← renameExpr f t
      let b' ← renameExpr f b
      let n' := f n
      pure (if n' == n then e.updateForallE! t' b' else .forallE n' t' b' bi)
    | .letE n t v b nd =>
      let t' ← renameExpr f t
      let v' ← renameExpr f v
      let b' ← renameExpr f b
      let n' := f n
      pure (if n' == n then e.updateLetE! t' v' b' else .letE n' t' v' b' nd)
    | .mdata d b =>
      let b' ← renameExpr f b
      let entries := d.entries.map fun (k, v) => (k, match v with
        | .ofName n => .ofName (f n)
        | v => v)
      let same := (d.entries.zip entries).all fun ((_, v), (_, v')) => match v, v' with
        | .ofName n, .ofName n' => n == n'
        | _, _ => true
      pure (if same then e.updateMData! b' else .mdata ⟨entries⟩ b')
    | .proj _ _ b => pure (e.updateProj! (← renameExpr f b))
    | _ => pure e
  modify (·.insert (ptrAddrUnsafe e) r)
  return r

/-! The state of an elaboration of the section variables. -/

/-- What decides an elaboration of the section variables besides the environment: equal in the
elaborations that a reuse replaces, but for the recursion depth, which is at most that of the
elaboration that is reused: the depth decides only whether the elaboration fails for it, as it fails
where the depth reaches the maximum, which one from a depth at most the maximum that did not fail
did not reach. -/
private structure Start where
  varDecls : Array Syntax
  varUIds : Array Name
  opts : Options
  levelNames : List Name
  isExporting : Bool
  isNoncomputable : Bool
  isMeta : Bool
  recDepth : Nat
  maxRecDepth : Nat
  currMacroScope : MacroScope
  nextMacroScope : MacroScope
  suppressElabErrors : Bool
  /-- Whether info trees are enabled, which decides those that the state holds at the end. -/
  infoEnabled : Bool

/-- Whether an elaboration that started at `b` can be replaced by the reuse of one that started at
`a`. -/
private def Start.same (a b : Start) : Bool :=
  a.varUIds == b.varUIds && a.levelNames == b.levelNames && a.isExporting == b.isExporting &&
    a.isNoncomputable == b.isNoncomputable && a.isMeta == b.isMeta && b.recDepth ≤ a.recDepth &&
    (a.maxRecDepth == 0 || a.recDepth ≤ a.maxRecDepth) &&
    a.maxRecDepth == b.maxRecDepth && a.currMacroScope == b.currMacroScope &&
    a.nextMacroScope == b.nextMacroScope && a.suppressElabErrors == b.suppressElabErrors &&
    a.infoEnabled == b.infoEnabled && a.opts == b.opts && a.varDecls.size == b.varDecls.size &&
    (a.varDecls.zip b.varDecls).all fun (x, y) => unsafe ptrEq x y || x == y

/-- What differs between `a` and `b`. -/
private def Start.difference (a b : Start) : String :=
  let d := [("universe names", a.levelNames == b.levelNames),
    ("visibility", a.isExporting == b.isExporting),
    ("kind of section", a.isNoncomputable == b.isNoncomputable && a.isMeta == b.isMeta),
    ("recursion depth", b.recDepth ≤ a.recDepth),
    ("maximal recursion depth", a.maxRecDepth == b.maxRecDepth),
    ("macro scope", a.currMacroScope == b.currMacroScope),
    ("next macro scope", a.nextMacroScope == b.nextMacroScope),
    ("syntax errors", a.suppressElabErrors == b.suppressElabErrors),
    ("info trees", a.infoEnabled == b.infoEnabled), ("options", a.opts == b.opts),
    ("binders", (a.varDecls.zip b.varDecls).all fun (x, y) => unsafe ptrEq x y || x == y)]
  ", ".intercalate (d.filterMap fun (w, same) => if same then none else some w)

/-- Where a reuse renames names of the elaboration's quotation context. -/
private structure Renames where
  /-- Variables whose names or types have some. -/
  fvars : Array FVarId := #[]
  /-- Metavariables whose names or types have some. -/
  mvarDecls : Array MVarId := #[]
  /-- Metavariables whose values have some. -/
  assigned : Array MVarId := #[]
  /-- The names of metavariables (`MetavarContext.userNames`) that are some. -/
  userNames : Array Name := #[]
  /-- The keys of entries of Lean's caches of `inferType` (`0`), `funInfo` (`1`), `whnf` (`3`) and
  `synthInstance` (`2`) that have some. -/
  cacheKeys : Array (UInt8 × NonScalar) := #[]

private def Renames.isEmpty (r : Renames) : Bool :=
  r.fvars.isEmpty && r.mvarDecls.isEmpty && r.assigned.isEmpty && r.userNames.isEmpty &&
    r.cacheKeys.isEmpty

/-- The state that an elaboration of the section variables ended with, with what it depended on. -/
private structure Entry where
  start : Start
  deps : EnvDeps.Deps
  /-- The module uses at the start (`moduleUses`), which the elaboration found. -/
  moduleUses : List ExtraModUse × List IndirectModUse
  /-- The prefix of the name generator's names, and its index after the elaboration: a reuse
  requires a generator of the same prefix at least there, whose names are none of the
  elaboration's. -/
  ngenPrefix : Name
  ngenEnd : Nat
  /-- The numbers of names and macro scopes that the elaboration took. -/
  names : Nat
  macroScopes : Nat
  /-- The quotation context of the elaboration, and where its names are. -/
  quotCtx : Name
  renames : Renames
  /-- The context at the end besides the local context: the recursion depth (from that at the
  start on) and the context of
  auto-bound implicits (`withAutoBoundImplicit`, which retries the elaboration with one more
  variable for each auto-bound implicit, and saves an info context if they are on). -/
  recDepth : Nat
  autoCtx : Option AutoBoundImplicitContext
  autoImplicit : Bool
  /-- The state at the end. -/
  lctx : LocalContext
  localInsts : LocalInstances
  xs : Array Expr
  sectionFVars : NameMap Expr
  metaState : Meta.State
  termState : Term.State
  coreCache : Core.Cache
  infoAssignment : PersistentHashMap MVarId InfoTree
  infoTrees : PersistentArray InfoTree
  /-- Where it was elaborated, for debugging. -/
  pos : String

/-- The entries (`empty` if none were put yet), out of the native store where they are kept
(`speculation.cpp`), which leaves it taken; none if it is taken, which turns reuse off. As those of
`TCCache.takeEntries`, they are not marked multi-threaded: one thread at a time uses them
(`TCCache.getEntries?`). -/
@[extern "lean_paperlean_take_store"]
private opaque takeEntries (slot : UInt8) (empty : Array Entry) : BaseIO (Option (Array Entry))

/-- Puts `es` into the native store of the entries, which `takeEntries` left taken. -/
@[extern "lean_paperlean_put_store"]
private opaque putEntries (slot : UInt8) (es : Array Entry) : BaseIO Unit

/-- The binders (`varDecls`, `varUIds`) and options whose elaboration could not be kept: they are
not recorded again, as their elaboration does the same. -/
private builtin_initialize unrecordableRef :
    IO.Ref (Array (Array Syntax × Array Name × Options × String)) ← IO.mkRef #[]

/-- Whether to report reuses on stderr (`PAPERLEAN_DEBUG_REUSE`). -/
private builtin_initialize debugReuse : Bool ← return (← IO.getEnv "PAPERLEAN_DEBUG_REUSE").isSome

private def maxEntries := 8

/-- Reused, elaborated, and elaborated because the dependencies of an entry did not hold. -/
private builtin_initialize statsRef : IO.Ref (Nat × Nat × Nat) ← IO.mkRef (0, 0, 0)

/-- Why elaborations were not kept, or entries not reused, with their numbers. -/
private builtin_initialize reasonsRef : Speculation.Reasons ← IO.mkRef {}

/-- The numbers of commands of this process whose section variables were reused, elaborated, and
elaborated because an earlier elaboration's dependencies did not hold. -/
def stats : BaseIO (Nat × Nat × Nat) := statsRef.get

/-- Why elaborations of this process were not kept, entries not reused, or elaborations left out
(`Speculation.Reasons.render`). -/
def reasons : BaseIO (List String) :=
  return (← reasonsRef.render) ++ (← Speculation.renderExclusions false)

private def noteReason (why : String) : TermElabM Unit := do
  let (fileMap, ref) := (← getFileMap, ← getRef)
  reasonsRef.note why fun _ => TCCache.posOf fileMap ref

/-- Counts an elaboration left out of reuse in the way `kind`, on any thread. -/
private def noteExcluded (kind : Speculation.Exclusion) : TermElabM Unit := do
  let (fileMap, ref) := (← getFileMap, ← getRef)
  Speculation.noteExclusion kind fun _ => TCCache.posOf fileMap ref

/-- Whether section variables may be reused under the options `opts`: on the command line, and not
with trace options or diagnostics, whose output reflects the elaboration. -/
private def reusableUnder (opts : Options) : Bool := Id.run do
  if !internal.cmdlineSnapshots.get opts || opts.getBool `diagnostics then
    return false
  for (n, v) in opts do
    if n.getRoot == `trace && v matches .ofBool true then
      return false
  return true

/-- The start of this elaboration of the section variables, if the state is the one that
`liftTermElabM` starts with, from which the elaborations that a reuse replaces start. -/
private def start? (varDecls : Array Syntax) (varUIds : Array Name) : TermElabM (Option Start) := do
  let mctx ← getMCtx
  let m ← getThe Meta.State
  let t ← get
  let c ← getThe Core.State
  unless (← getLCtx).isEmpty && (← getLocalInstances).isEmpty && mctx.decls.isEmpty &&
      mctx.lDecls.isEmpty && mctx.mvarCounter == 0 && mctx.lmvarCounter == 0 && mctx.depth == 0 &&
      m.cache.inferType.isEmpty && m.cache.whnf.isEmpty && m.cache.synthInstance.isEmpty &&
      m.cache.funInfo.isEmpty && m.postponed.isEmpty && t.syntheticMVars.isEmpty &&
      t.pendingMVars.isEmpty && t.mvarErrorInfos.isEmpty && t.levelMVarErrorInfos.isEmpty &&
      t.mvarArgNames.isEmpty && t.letRecsToLift.isEmpty && c.infoState.trees.isEmpty &&
      c.infoState.assignment.isEmpty do
    return none
  let ctx ← readThe Core.Context
  let tctx ← read
  return some {
    varDecls, varUIds, opts := ctx.options, levelNames := t.levelNames
    isExporting := c.env.isExporting, isNoncomputable := tctx.isNoncomputableSection
    isMeta := tctx.isMetaSection, recDepth := ctx.currRecDepth, maxRecDepth := ctx.maxRecDepth
    currMacroScope := ctx.currMacroScope, nextMacroScope := c.nextMacroScope
    suppressElabErrors := ctx.suppressElabErrors, infoEnabled := c.infoState.enabled }

/-- Where the local context `lctx`, the state `ms` of `MetaM` and the caches of `CoreM` have names
of the quotation context `isCtx`: the renames, or why a reuse could not rename them all. -/
private unsafe def renames? (isCtx : Name → Bool) (lctx : LocalContext) (ms : Meta.State)
    (coreCache : Core.Cache) (levelNames : List Name) : Except String Renames := do
  let scan (e : Expr) : StateM (Std.HashMap USize UInt8) UInt8 := scanExpr isCtx e
  let run : StateM (Std.HashMap USize UInt8) (Except String Renames) := do
    let mut r : Renames := {}
    let blocked := "names with macro scopes of the quotation context that a reuse cannot rename"
    for d in lctx do
      let mut s := if isCtx d.userName then 1 else 0
      s := max s (← scan d.type)
      if let some v := d.value? then s := max s (← scan v)
      if s == 2 then return .error blocked
      if s == 1 then r := { r with fvars := r.fvars.push d.fvarId }
    let mctx := ms.mctx
    for (id, d) in mctx.decls do
      let s := max (if isCtx d.userName then 1 else 0) (← scan d.type)
      if s == 2 then return .error blocked
      if s == 1 then r := { r with mvarDecls := r.mvarDecls.push id }
    for (id, v) in mctx.eAssignment do
      let s ← scan v
      if s == 2 then return .error blocked
      if s == 1 then r := { r with assigned := r.assigned.push id }
    for (_, u) in mctx.lAssignment do
      if levelOfCtx isCtx u then return .error blocked
    for (n, _) in mctx.userNames do
      if isCtx n then r := { r with userNames := r.userNames.push n }
    for (k, v) in ms.cache.inferType do
      let s := max (← scan k.expr) (← scan v)
      if s == 2 then return .error blocked
      if s == 1 then r := { r with cacheKeys := r.cacheKeys.push (0, unsafeCast k) }
    for (k, v) in ms.cache.whnf do
      let s := max (← scan k.expr) (← scan v)
      if s == 2 then return .error blocked
      if s == 1 then r := { r with cacheKeys := r.cacheKeys.push (3, unsafeCast k) }
    for (k, _) in ms.cache.funInfo do
      let s ← scan k.expr
      if s == 2 then return .error blocked
      if s == 1 then r := { r with cacheKeys := r.cacheKeys.push (1, unsafeCast k) }
    for (k, v) in ms.cache.synthInstance do
      let mut s ← scan k.type
      for li in k.localInsts do s := max s (← scan li.fvar)
      if let some v := v then
        s := max s (← scan v.expr)
        for m in v.mvars do s := max s (← scan m)
        if v.paramNames.any isCtx then s := 2
      if s == 2 then return .error blocked
      if s == 1 then r := { r with cacheKeys := r.cacheKeys.push (2, unsafeCast k) }
    for (_, v) in coreCache.instLevelType do
      if (← scan v.2) != 0 then return .error blocked
    for (_, v) in coreCache.instLevelValue do
      if (← scan v.2) != 0 then return .error blocked
    if levelNames.any isCtx then return .error blocked
    return .ok r
  run.run' {}

/-- `m` without `k`, unless the fault `fault` is `stale-cache` (for testing the oracle). -/
private def eraseUnlessFault {α β : Type} [BEq α] [Hashable α] (fault : String)
    (m : PersistentHashMap α β) (k : α) : PersistentHashMap α β :=
  if fault == "stale-cache" then m else m.erase k

/-- The state of `e` with the names of its quotation context renamed to those of `quotCtx`: the
local context, and the state of `MetaM`, with the fault `fault`. -/
private unsafe def renamed (fault : String) (e : Entry) (quotCtx : Name) :
    LocalContext × Meta.State := Id.run do
  if quotCtx == e.quotCtx || e.renames.isEmpty then
    return (e.lctx, e.metaState)
  let f := renameName (comps e.quotCtx) (comps quotCtx)
  let go : StateM (Std.HashMap USize Expr) (LocalContext × Meta.State) := do
    let r := e.renames
    let mut lctx := e.lctx
    for id in r.fvars do
      let some d := lctx.find? id | continue
      let d ← match d with
        | .cdecl i id n t bi k => pure (.cdecl i id (f n) (← renameExpr f t) bi k)
        | .ldecl i id n t v nd k =>
          pure (.ldecl i id (f n) (← renameExpr f t) (← renameExpr f v) nd k)
      lctx := lctx.modifyLocalDecl id fun _ => d
    let mut mctx := e.metaState.mctx
    for id in r.mvarDecls do
      let some d := mctx.decls.find? id | continue
      let type ← renameExpr f d.type
      mctx := { mctx with decls := mctx.decls.insert id { d with userName := f d.userName, type } }
    for id in r.assigned do
      let some v := mctx.eAssignment.find? id | continue
      mctx := { mctx with eAssignment := mctx.eAssignment.insert id (← renameExpr f v) }
    for n in r.userNames do
      let some id := mctx.userNames.find? n | continue
      mctx := { mctx with userNames := (mctx.userNames.erase n).insert (f n) id }
    let mut cache := e.metaState.cache
    for (c, k) in r.cacheKeys do
      if c == 0 || c == 3 then
        let k : ExprConfigCacheKey := unsafeCast k
        let found? := if c == 0 then cache.inferType.find? k else cache.whnf.find? k
        let some v := found? | continue
        let expr ← renameExpr f k.expr
        let v ← renameExpr f v
        let k' := { k with expr }
        -- (the keys compare binder names, `Expr.equal`: the entry under the earlier key would be
        -- one that Lean does not make, as the local context is renamed)
        cache := if c == 0 then
            { cache with inferType := (eraseUnlessFault fault cache.inferType k).insert k' v }
          else { cache with whnf := (eraseUnlessFault fault cache.whnf k).insert k' v }
      else if c == 1 then
        if fault == "stale-fun-info" then continue
        let k : InfoCacheKey := unsafeCast k
        let some v := cache.funInfo.find? k | continue
        let expr ← renameExpr f k.expr
        cache := { cache with funInfo := (cache.funInfo.erase k).insert { k with expr } v }
      else
        let k : SynthInstanceCacheKey := unsafeCast k
        let some v := cache.synthInstance.find? k | continue
        let type ← renameExpr f k.type
        let localInsts ← k.localInsts.mapM fun li => do
          let fvar ← renameExpr f li.fvar
          return { li with fvar }
        let v ← v.mapM fun v => do
          let expr ← renameExpr f v.expr
          let mvars ← v.mvars.mapM (renameExpr f)
          return { v with expr, mvars }
        cache := { cache with
          synthInstance := (cache.synthInstance.erase k).insert { k with type, localInsts } v }
    return (lctx, { e.metaState with mctx, cache })
  return go.run' {}

/-! The identifiers of a reuse: those of Lean's elaboration, which takes the same names of the
generator at its current index. -/

/-- `n` with the names that a generator of prefix `p` gave from index `start` on (`count` of them,
and the names of generators made from them) renumbered to start at `to`. -/
private partial def shiftName (p : Name) (start to count : Nat) : Name → Name
  | .num q i =>
    if q == p && start ≤ i && i < start + count then .num q (i - start + to)
    else .num (shiftName p start to count q) i
  | .str q s => .str (shiftName p start to count q) s
  | .anonymous => .anonymous

private partial def shiftLevel (f : Name → Name) : Level → Level
  | .mvar id => .mvar ⟨f id.name⟩
  | .succ u => .succ (shiftLevel f u)
  | .max u v => .max (shiftLevel f u) (shiftLevel f v)
  | .imax u v => .imax (shiftLevel f u) (shiftLevel f v)
  | u => u

/-- What a remap has done, by address: the state shares expressions, local contexts and metavariable
contexts. -/
private structure RemapState where
  exprs : Std.HashMap USize Expr := {}
  lctxs : Std.HashMap USize LocalContext := {}
  mctxs : Std.HashMap USize MetavarContext := {}

/-- A remap of identifiers by a function on their names. -/
private abbrev RemapM := ReaderT (Name → Name) (StateM RemapState)

private unsafe def rmExpr (e : Expr) : RemapM Expr := do
  if !e.hasFVar && !e.hasMVar then
    return e
  let k := ptrAddrUnsafe e
  if let some r := (← get).exprs[k]? then
    return r
  let r ← match e with
    | .fvar id => pure (.fvar ⟨(← read) id.name⟩)
    | .mvar id => pure (.mvar ⟨(← read) id.name⟩)
    | .sort u => pure (.sort (shiftLevel (← read) u))
    | .const n us => pure (.const n (us.map (shiftLevel (← read))))
    | .app f a => pure (e.updateApp! (← rmExpr f) (← rmExpr a))
    | .lam _ t b _ => pure (e.updateLambdaE! (← rmExpr t) (← rmExpr b))
    | .forallE _ t b _ => pure (e.updateForallE! (← rmExpr t) (← rmExpr b))
    | .letE _ t v b _ => pure (e.updateLetE! (← rmExpr t) (← rmExpr v) (← rmExpr b))
    | .mdata _ b => pure (e.updateMData! (← rmExpr b))
    | .proj _ _ b => pure (e.updateProj! (← rmExpr b))
    | _ => pure e
  modify fun s => { s with exprs := s.exprs.insert k r }
  return r

private def rmFVar (id : FVarId) : RemapM FVarId := return ⟨(← read) id.name⟩
private def rmMVar (id : MVarId) : RemapM MVarId := return ⟨(← read) id.name⟩
private def rmLMVar (id : LMVarId) : RemapM LMVarId := return ⟨(← read) id.name⟩

private unsafe def rmLocalDecl : LocalDecl → RemapM LocalDecl
  | .cdecl i id n t bi k => return .cdecl i (← rmFVar id) n (← rmExpr t) bi k
  | .ldecl i id n t v nd k => return .ldecl i (← rmFVar id) n (← rmExpr t) (← rmExpr v) nd k

private unsafe def rmLCtx (lctx : LocalContext) : RemapM LocalContext := do
  if lctx.isEmpty then
    return lctx
  let k := ptrAddrUnsafe lctx
  if let some r := (← get).lctxs[k]? then
    return r
  let decls ← lctx.decls.mapM (·.mapM rmLocalDecl)
  let fvarIdToDecl := decls.foldl (init := {}) fun m d? => match d? with
    | some d => m.insert d.fvarId d
    | none => m
  let auxDeclToFullName ← lctx.auxDeclToFullName.toList.foldlM (init := {}) fun m (id, n) =>
    return m.insert (← rmFVar id) n
  let r : LocalContext := { fvarIdToDecl, decls, auxDeclToFullName }
  modify fun s => { s with lctxs := s.lctxs.insert k r }
  return r

private unsafe def rmLocalInsts (ls : LocalInstances) : RemapM LocalInstances :=
  ls.mapM fun li => return { li with fvar := ← rmExpr li.fvar }

private unsafe def rmMCtx (m : MetavarContext) : RemapM MetavarContext := do
  let k := ptrAddrUnsafe m
  if let some r := (← get).mctxs[k]? then
    return r
  let f ← read
  let lDecls ← m.lDecls.foldlM (init := {}) fun acc id d => return acc.insert (← rmLMVar id) d
  let decls ← m.decls.foldlM (init := {}) fun acc id d => do
    return acc.insert (← rmMVar id) { d with
      lctx := ← rmLCtx d.lctx, type := ← rmExpr d.type
      localInstances := ← rmLocalInsts d.localInstances }
  let userNames ← m.userNames.foldlM (init := {}) fun acc n id => return acc.insert n (← rmMVar id)
  let lAssignment ← m.lAssignment.foldlM (init := {}) fun acc id u =>
    return acc.insert (← rmLMVar id) (shiftLevel f u)
  let eAssignment ← m.eAssignment.foldlM (init := {}) fun acc id v =>
    return acc.insert (← rmMVar id) (← rmExpr v)
  let dAssignment ← m.dAssignment.foldlM (init := {}) fun acc id d => do
    return acc.insert (← rmMVar id) { d with
      fvars := ← d.fvars.mapM rmExpr, mvarIdPending := ← rmMVar d.mvarIdPending }
  let instanceTypedMVars ← m.instanceTypedMVars.foldlM (init := {}) fun acc id u =>
    return acc.insert (← rmMVar id) u
  let r := { m with
    lDecls, decls, userNames, lAssignment, eAssignment, dAssignment, instanceTypedMVars }
  modify fun s => { s with mctxs := s.mctxs.insert k r }
  return r

/-- Update only remapped entries, retaining the original map when none change. Remove every old
and destination key first, then replay affected entries in the original traversal order. This also
preserves the old rebuild's last-insertion winner if a moved key collides with an unchanged key,
or with another moved key; simply erasing/inserting during one fold would not. -/
private def rmCacheMap {α β : Type} [BEq α] [Hashable α]
    (cache : PersistentHashMap α β) (remap : α → β → RemapM (Option (α × β))) :
    RemapM (PersistentHashMap α β) := do
  let changes ← cache.foldlM (init := ({} : PersistentHashMap α (α × β))) fun changes k v => do
    match ← remap k v with
    | some kv => return changes.insert k kv
    | none => return changes
  if changes.isEmpty then return cache
  let affected := changes.foldl (init := ({} : PersistentHashMap α Unit)) fun keys k (k', _) =>
    (keys.insert k ()).insert k' ()
  let out := affected.foldl (init := cache) fun out k _ => out.erase k
  return cache.foldl (init := out) fun out k v =>
    match changes.find? k with
    | some (k', v') => out.insert k' v'
    | none => if affected.contains k then out.insert k v else out

private unsafe def rmCache (c : Meta.Cache) : RemapM Meta.Cache := do
  let hasId := fun (x : Expr) => x.hasFVar || x.hasMVar
  let inferType ← rmCacheMap c.inferType fun k v => do
    unless hasId k.expr || hasId v do return none
    let expr ← rmExpr k.expr
    let value ← rmExpr v
    if expr.equal k.expr && value.equal v then return none
    return some ({ k with expr }, value)
  -- (few keys of these have identifiers: `whnf` caches closed terms, `funInfo` mostly constants)
  let whnf ← c.whnf.foldlM (init := c.whnf) fun acc k v => do
    if hasId k.expr then
      return (acc.erase k).insert { k with expr := ← rmExpr k.expr } (← rmExpr v)
    else if hasId v then
      return acc.insert k (← rmExpr v)
    else
      return acc
  let funInfo ← c.funInfo.foldlM (init := c.funInfo) fun acc k v => do
    if hasId k.expr then
      return (acc.erase k).insert { k with expr := ← rmExpr k.expr } v
    else
      return acc
  let synthInstance ← rmCacheMap c.synthInstance fun k v => do
    let keyHasId := hasId k.type || k.localInsts.any (hasId ·.fvar)
    let valueHasId := v.any fun r => hasId r.expr || r.mvars.any hasId
    unless keyHasId || valueHasId do return none
    let k' ← if keyHasId then
        pure { k with type := ← rmExpr k.type, localInsts := ← rmLocalInsts k.localInsts }
      else pure k
    let v' ← if valueHasId then
        v.mapM fun r => return { r with expr := ← rmExpr r.expr, mvars := ← r.mvars.mapM rmExpr }
      else pure v
    let sameKey := k'.type.equal k.type && k'.localInsts.size == k.localInsts.size &&
      (k'.localInsts.zip k.localInsts).all fun (a, b) => a.fvar.equal b.fvar
    let sameValue := match v', v with
      | some a, some b => a.expr.equal b.expr && a.mvars.size == b.mvars.size &&
        (a.mvars.zip b.mvars).all fun (x, y) => x.equal y
      | none, none => true
      | _, _ => false
    if sameKey && sameValue then return none
    return some (k', v')
  return { c with inferType, whnf, funInfo, synthInstance }

private unsafe def rmDefEqContext (c : DefEqContext) : RemapM DefEqContext :=
  return { c with
    lhs := ← rmExpr c.lhs, rhs := ← rmExpr c.rhs, lctx := ← rmLCtx c.lctx
    localInstances := ← rmLocalInsts c.localInstances }

private unsafe def rmMetaState (ms : Meta.State) : RemapM Meta.State := do
  let f ← read
  let postponed ← ms.postponed.mapM fun p => return { p with
    lhs := shiftLevel f p.lhs, rhs := shiftLevel f p.rhs
    ctx? := ← p.ctx?.mapM rmDefEqContext }
  return { ms with mctx := ← rmMCtx ms.mctx, cache := ← rmCache ms.cache, postponed }

private unsafe def rmTermState (t : Term.State) : RemapM Term.State := do
  let syntheticMVars ← t.syntheticMVars.toList.foldlM (init := {}) fun m (id, d) =>
    return m.insert (← rmMVar id) d
  let mvarErrorInfos ← t.mvarErrorInfos.mapM fun i => do
    let kind ← match i.kind with
      | .implicitArg lctx ctx => pure (.implicitArg (← rmLCtx lctx) (← rmExpr ctx))
      | k => pure k
    return { i with mvarId := ← rmMVar i.mvarId, kind }
  let levelMVarErrorInfos ← t.levelMVarErrorInfos.mapM fun i =>
    return { i with lctx := ← rmLCtx i.lctx, expr := ← rmExpr i.expr }
  let mvarArgNames ← t.mvarArgNames.toList.foldlM (init := {}) fun m (id, n) =>
    return m.insert (← rmMVar id) n
  return { t with
    syntheticMVars, pendingMVars := ← t.pendingMVars.mapM rmMVar, mvarErrorInfos
    levelMVarErrorInfos, mvarArgNames }

private unsafe def rmTermInfo (i : TermInfo) : RemapM TermInfo :=
  return { i with
    lctx := ← rmLCtx i.lctx, expectedType? := ← i.expectedType?.mapM rmExpr
    expr := ← rmExpr i.expr }

private unsafe def rmCompletionInfo : CompletionInfo → RemapM CompletionInfo
  | .dot i t? => return .dot (← rmTermInfo i) (← t?.mapM rmExpr)
  | .id stx id dot lctx t? => return .id stx id dot (← rmLCtx lctx) (← t?.mapM rmExpr)
  | .dotId stx id lctx t? => return .dotId stx id (← rmLCtx lctx) (← t?.mapM rmExpr)
  | .fieldId stx id lctx n => return .fieldId stx id (← rmLCtx lctx) n
  | i => return i

/-- (Custom info is opaque: messages and meta-code that read it see the recording's identifiers.) -/
private unsafe def rmInfo : Info → RemapM Info
  | .ofTermInfo i => return .ofTermInfo (← rmTermInfo i)
  | .ofPartialTermInfo i => return .ofPartialTermInfo { i with
    lctx := ← rmLCtx i.lctx, expectedType? := ← i.expectedType?.mapM rmExpr }
  | .ofDelabTermInfo i => return .ofDelabTermInfo { i with toTermInfo := ← rmTermInfo i.toTermInfo }
  | .ofMacroExpansionInfo i => return .ofMacroExpansionInfo { i with lctx := ← rmLCtx i.lctx }
  | .ofFieldInfo i => return .ofFieldInfo { i with lctx := ← rmLCtx i.lctx, val := ← rmExpr i.val }
  | .ofFVarAliasInfo i => return .ofFVarAliasInfo { i with
    id := ← rmFVar i.id, baseId := ← rmFVar i.baseId }
  | .ofCompletionInfo i => return .ofCompletionInfo (← rmCompletionInfo i)
  | .ofTacticInfo i => return .ofTacticInfo { i with
    mctxBefore := ← rmMCtx i.mctxBefore, goalsBefore := ← i.goalsBefore.mapM rmMVar
    mctxAfter := ← rmMCtx i.mctxAfter, goalsAfter := ← i.goalsAfter.mapM rmMVar }
  | i => return i

private unsafe def rmInfoTree (shift : Nat → Nat) : InfoTree → RemapM InfoTree
  | .context i t => do
    let i' ← match i with
      | .commandCtx c => pure (.commandCtx { c with
        mctx := ← rmMCtx c.mctx, ngen.idx := shift c.ngen.idx })
      | .autoImplicitCtx es => pure (.autoImplicitCtx (← es.mapM rmExpr))
      | i => pure i
    return .context i' (← rmInfoTree shift t)
  | .node i cs => return .node (← rmInfo i) (← cs.mapM (rmInfoTree shift))
  | .hole id => return .hole (← rmMVar id)

/-- The state at the end of an elaboration of section variables as a reuse sets it. -/
private structure Reused where
  lctx : LocalContext
  localInsts : LocalInstances
  xs : Array Expr
  sectionFVars : NameMap Expr
  metaState : Meta.State
  termState : Term.State
  infoAssignment : PersistentHashMap MVarId InfoTree
  infoTrees : PersistentArray InfoTree
  autoCtx : Option AutoBoundImplicitContext

private local instance : Inhabited Reused :=
  ⟨⟨default, default, default, default, default, default, default, default, default⟩⟩

/-- The state of the reuse of `e`, whose names of the quotation context `lctx` and `ms` have renamed,
with the identifiers that Lean's elaboration from index `idx` of the name generator gives. -/
private unsafe def remapped (e : Entry) (lctx : LocalContext) (ms : Meta.State) (idx : Nat) :
    Reused :=
  let start := e.ngenEnd - e.names
  let shift (i : Nat) : Nat := if start ≤ i && i ≤ e.ngenEnd then i - start + idx else i
  let go : RemapM Reused := do
    return {
      lctx := ← rmLCtx lctx, localInsts := ← rmLocalInsts e.localInsts, xs := ← e.xs.mapM rmExpr
      sectionFVars := ← e.sectionFVars.toList.foldlM (init := {}) fun m (n, x) =>
        return m.insert n (← rmExpr x)
      metaState := ← rmMetaState ms, termState := ← rmTermState e.termState
      infoAssignment := ← e.infoAssignment.foldlM (init := {}) fun m id t =>
        return m.insert (← rmMVar id) (← rmInfoTree shift t)
      infoTrees := ← e.infoTrees.mapM (rmInfoTree shift)
      autoCtx := ← e.autoCtx.mapM fun c =>
        return { c with boundVariables := ← c.boundVariables.mapM rmExpr } }
  (go (shiftName e.ngenPrefix start idx e.names)).run' {}


/-! The oracle (`PAPERLEAN_REUSE_ORACLE`). -/

/-- The state at the end of an elaboration of the section variables, as the oracle compares it. -/
private structure Ended where
  lctx : LocalContext
  localInsts : LocalInstances
  xs : Array Expr
  sectionFVars : NameMap Expr
  metaState : Meta.State
  termState : Term.State
  coreCache : Core.Cache
  infoTrees : Nat
  names : Nat
  macroScopes : Nat

/-- The number of entries of `m`. -/
private def count {α β : Type} [BEq α] [Hashable α] (m : PersistentHashMap α β) : Nat :=
  m.foldl (fun n _ _ => n + 1) 0

private partial def levelMentions (p : LMVarId → Bool) : Level → Bool
  | .mvar id => p id
  | .succ u => levelMentions p u
  | .max u v | .imax u v => levelMentions p u || levelMentions p v
  | _ => false

/-- Compares the state `ours` of a reuse with `lean`'s, which Lean's elaboration ended with (`ren`
renames the names of its quotation context to those of the reuse's, where the reuse does not rename
them); the first difference, if any. -/
private unsafe def difference? (ren : Name → Name) (ours lean : Ended) : Option String := Id.run do
  let ex (a b : Expr) : Bool := a.equal b
  -- (names and expressions that a reuse does not rename)
  let exR (a b : Expr) : Bool := a.equal (renameExprPure ren b)
  let sameDecl (exr : Expr → Expr → Bool) (nm : Name → Name) (a b : LocalDecl) : Bool :=
    a.index == b.index && a.fvarId == b.fvarId && a.userName == nm b.userName &&
      exr a.type b.type && a.binderInfo == b.binderInfo && a.kind == b.kind &&
      match a.value?, b.value? with
      | some x, some y => exr x y
      | none, none => true
      | _, _ => false
  let sameLCtx (exr : Expr → Expr → Bool) (nm : Name → Name) (a b : LocalContext) : Bool :=
    a.decls.size == b.decls.size &&
      (a.decls.toArray.zip b.decls.toArray).all fun
        | (some x, some y) => sameDecl exr nm x y
        | (none, none) => true
        | _ => false
  let sameInsts (a b : LocalInstances) : Bool :=
    a.size == b.size && (a.zip b).all fun (x, y) => x.className == y.className && ex x.fvar y.fvar
  if ours.names != lean.names || ours.macroScopes != lean.macroScopes then
    return some s!"names {ours.names} and macro scopes {ours.macroScopes}, Lean's \
      {lean.names} and {lean.macroScopes}"
  unless sameLCtx ex id ours.lctx lean.lctx do return some "the local context"
  unless sameInsts ours.localInsts lean.localInsts do return some "the local instances"
  unless ours.xs.size == lean.xs.size && (ours.xs.zip lean.xs).all (fun (a, b) => ex a b) &&
      ours.sectionFVars.toList.length == lean.sectionFVars.toList.length &&
      (ours.sectionFVars.toList.zip lean.sectionFVars.toList).all
        (fun ((u, a), (v, b)) => u == v && ex a b) do
    return some "the variables"
  let m := ours.metaState.mctx
  let l := lean.metaState.mctx
  unless m.depth == l.depth && m.levelAssignDepth == l.levelAssignDepth &&
      m.mvarCounter == l.mvarCounter && m.lmvarCounter == l.lmvarCounter &&
      count m.decls == count l.decls && count m.lDecls == count l.lDecls &&
      count m.eAssignment == count l.eAssignment && count m.lAssignment == count l.lAssignment &&
      count m.dAssignment == count l.dAssignment && count m.userNames == count l.userNames &&
      count m.instanceTypedMVars == count l.instanceTypedMVars do
    return some "the numbers of the metavariable context"
  for (id, d) in l.decls do
    let some d' := m.decls.find? id | return some "a metavariable"
    unless d'.userName == d.userName && ex d'.type d.type && d'.depth == d.depth &&
        d'.kind.ctorIdx == d.kind.ctorIdx && d'.numScopeArgs == d.numScopeArgs &&
        d'.index == d.index &&
        sameInsts d'.localInstances d.localInstances && sameLCtx exR ren d'.lctx d.lctx do
      return some "the declaration of a metavariable"
  for (id, d) in l.lDecls do
    let some d' := m.lDecls.find? id | return some "a universe metavariable"
    unless d'.depth == d.depth do return some "the declaration of a universe metavariable"
  for (id, v) in l.eAssignment do
    let some v' := m.eAssignment.find? id | return some "an assignment"
    unless ex v' v do return some "the value of a metavariable"
  for (id, v) in l.lAssignment do
    let some v' := m.lAssignment.find? id | return some "a universe assignment"
    unless v' == v do return some "the value of a universe metavariable"
  for (n, id) in l.userNames do
    unless m.userNames.find? n == some id do return some "a metavariable's name"
  for (id, _) in l.instanceTypedMVars do
    unless m.instanceTypedMVars.contains id do return some "an instance-typed metavariable"
  let t := ours.termState
  let u := lean.termState
  unless t.levelNames == u.levelNames &&
      t.syntheticMVars.toList.length == u.syntheticMVars.toList.length &&
      u.syntheticMVars.toList.all (fun (id, d) => (t.syntheticMVars.get? id).any
        (toString ·.kind == toString d.kind)) &&
      t.letRecsToLift.isEmpty && u.letRecsToLift.isEmpty &&
      t.pendingMVars == u.pendingMVars &&
      t.mvarErrorInfos.map (·.mvarId) == u.mvarErrorInfos.map (·.mvarId) &&
      t.mvarErrorInfos.map (toString ·.kind) == u.mvarErrorInfos.map (toString ·.kind) &&
      t.levelMVarErrorInfos.length == u.levelMVarErrorInfos.length &&
      t.mvarArgNames.toList.length == u.mvarArgNames.toList.length &&
      u.mvarArgNames.toList.all (fun (id, n) => t.mvarArgNames.get? id == some (ren n)) do
    return some "the state of the elaboration"
  -- (Lean's caches of `MetaM`: every entry of the reuse's must be the one that Lean's elaboration
  -- makes, unless no later lookup can find it, as its key mentions a variable or metavariable that
  -- is not in the state: the reuse's and Lean's elaborations may have reused other typeclass
  -- searches, `Lean.PaperLean.TCCache`, which leaves out such entries. Lean's entries may be
  -- missing from the reuse's: a missing entry only costs a recomputation.)
  let c := ours.metaState.cache
  let d := lean.metaState.cache
  let mut fvars : Std.HashMap FVarId Unit := {}
  for decl in ours.lctx do
    fvars := fvars.insert decl.fvarId ()
  for (_, md) in m.decls do
    for decl in md.lctx do
      fvars := fvars.insert decl.fvarId ()
  let liveLevel (u : Level) : Bool := !levelMentions (!m.lDecls.contains ·) u
  let live (e : Expr) : Bool := (e.find? fun
    | .fvar id => !fvars.contains id
    | .mvar id => !m.decls.contains id
    | .sort u => !liveLevel u
    | .const _ us => us.any (!liveLevel ·)
    | _ => false).isNone
  let sameAbst (a b : Option AbstractMVarsResult) : Bool := match a, b with
    | some a, some b =>
      ex a.expr b.expr && a.paramNames == b.paramNames && a.numMVars == b.numMVars &&
        a.mvars.size == b.mvars.size && (a.mvars.zip b.mvars).all fun (x, y) => ex x y
    | none, none => true
    | _, _ => false
  let sameFunInfo (w v : FunInfo) : Bool :=
    w.resultDeps == v.resultDeps && w.paramInfo.size == v.paramInfo.size &&
      (w.paramInfo.zip v.paramInfo).all fun (x, y) => x.binderInfo == y.binderInfo &&
        x.hasFwdDeps == y.hasFwdDeps && x.backDeps == y.backDeps && x.isProp == y.isProp &&
        x.isDecInst == y.isDecInst && x.isInstance == y.isInstance &&
        x.higherOrderOutParam == y.higherOrderOutParam &&
        x.dependsOnHigherOrderOutParam == y.dependsOnHigherOrderOutParam
  for (k, v) in c.inferType do
    match d.inferType.find? k with
    | some w => unless ex v w do return some "an entry of the cache of `inferType`"
    | none => if live k.expr then
        return some "an entry of the cache of `inferType` that Lean's elaboration does not make"
  for (k, v) in c.whnf do
    match d.whnf.find? k with
    | some w => unless ex v w do return some "an entry of the cache of `whnf`"
    | none => if live k.expr then
        return some "an entry of the cache of `whnf` that Lean's elaboration does not make"
  for (k, v) in c.synthInstance do
    match d.synthInstance.find? k with
    | some w => unless sameAbst v w do return some "an entry of the cache of `synthInstance`"
    | none => if live k.type && k.localInsts.all (live ·.fvar) then
        return some "an entry of the cache of `synthInstance` that Lean's elaboration does not make"
  for (k, v) in c.funInfo do
    -- (the cache takes keys with other binder names as the same; Lean's other caches do not)
    match d.funInfo.findEntry? k with
    | some (k', w) =>
      unless ex k.expr k'.expr && sameFunInfo v w do
        return some "an entry of the cache of `getFunInfo`"
    | none => if live k.expr then
        return some "an entry of the cache of `getFunInfo` that Lean's elaboration does not make"
  -- (the caches of `isDefEq` are not set by a reuse)
  unless c.defEqTrans.isEmpty && c.defEqPerm.isEmpty do
    return some "the caches of `isDefEq`"
  let p := ours.metaState.postponed
  let q := lean.metaState.postponed
  unless p.size == q.size && (p.toArray.zip q.toArray).all fun (x, y) =>
      x.lhs == y.lhs && x.rhs == y.rhs do
    return some "the postponed universe constraints"
  unless ours.infoTrees == lean.infoTrees do
    return some "the number of info trees"
  return none
where
  /-- `e` with the binder names and the names in metadata renamed by `f`. -/
  renameExprPure (f : Name → Name) (e : Expr) : Expr :=
    (renameExpr f e).run' {}

/-- Compares the reuse of entry `e`, whose state as a reuse sets it is `r`, with Lean's elaboration
(`elabVars`) from the current state, which it leaves as it was. -/
private unsafe def oracle (e : Entry) (r : Reused)
    (elabVars : ∀ {β}, (Array Expr → NameMap Expr → TermElabM β) → TermElabM β) :
    TermElabM Unit := do
  let core0 ← getThe Core.State
  let meta0 ← getThe Meta.State
  let term0 ← get
  let paused ← envPause
  -- (no typeclass result is reused in it either)
  let lean? ← Speculation.withoutReuse do try
      some <$> elabVars fun xs sectionFVars => do
        let core1 ← getThe Core.State
        return ({
          lctx := ← getLCtx, localInsts := ← getLocalInstances, xs, sectionFVars
          metaState := ← getThe Meta.State, termState := ← get, coreCache := core1.cache
          infoTrees := core1.infoState.trees.size
          names := core1.ngen.idx - core0.ngen.idx
          macroScopes := core1.nextMacroScope - core0.nextMacroScope } : Ended)
    catch _ => pure none
  envResume paused
  set term0
  modifyThe Meta.State fun _ => meta0
  modifyThe Core.State fun _ => core0
  let some lean := lean? | Speculation.fail "section variables: their elaboration fails"
  let ours : Ended := {
    lctx := r.lctx, localInsts := r.localInsts, xs := r.xs, sectionFVars := r.sectionFVars
    metaState := r.metaState, termState := r.termState, coreCache := e.coreCache
    infoTrees := e.infoTrees.size, names := e.names, macroScopes := e.macroScopes }
  let ren := renameName (comps (← MonadQuotation.getContext)) (comps e.quotCtx)
  if let some why := difference? ren ours lean then
    Speculation.fail s!"section variables: elaborated differently ({why})"
  -- (each entry of the caches of `CoreM` must be its constant's type or value for its levels)
  let env ← getEnv
  for (n, us, v) in e.coreCache.instLevelType do
    unless (env.find? n).any (·.instantiateTypeLevelParams us |>.equal v) do
      Speculation.fail s!"section variables: an entry of the cache of `CoreM` for {n}"
  for (n, us, v) in e.coreCache.instLevelValue do
    unless (env.find? n).any fun c => c.hasValue (allowOpaque := true) &&
        (c.instantiateValueLevelParams! us (allowOpaque := true)).equal v do
      Speculation.fail s!"section variables: an entry of the cache of `CoreM` for {n}"

/-! Recording and reuse. -/

/-- The entry for the elaboration that started at `start` with the states `core0` and `meta0`, the
module uses `moduleUses` and in the quotation context `quotCtx`, now ended with the variables `xs`
and the dependencies `deps?`, or why it is not kept. -/
private def entry? (start : Start) (core0 : Core.State) (meta0 : Meta.State)
    (moduleUses : List ExtraModUse × List IndirectModUse)
    (quotCtx : Name) (deps? : Except String EnvDeps.Raw) (xs : Array Expr)
    (sectionFVars : NameMap Expr) (pos : String) : TermElabM (Except String Entry) := do
  let deps ← match deps? with
    | .ok deps => pure deps.deps
    | .error why => return .error s!"not recordable: {why}"
  let core1 ← getThe Core.State
  let meta1 ← getThe Meta.State
  let term1 ← get
  let lctx ← getLCtx
  unless unsafe ptrEq core1.env core0.env do
    return .error "a change of the environment"
  unless unsafe ptrEq core1.traceState core0.traceState &&
      ptrEq core1.auxDeclNGen core0.auxDeclNGen && ptrEq core1.snapshotTasks core0.snapshotTasks &&
      ptrEq core1.infoState.lazyAssignment core0.infoState.lazyAssignment &&
      core1.infoState.enabled == core0.infoState.enabled &&
      ptrEq meta1.zetaDeltaFVarIds meta0.zetaDeltaFVarIds && ptrEq meta1.diag meta0.diag do
    return .error "a change of the state"
  unless core1.ngen.namePrefix == core0.ngen.namePrefix && core0.ngen.idx ≤ core1.ngen.idx do
    return .error "another name generator"
  let mctx := meta1.mctx
  -- (a pending typeclass problem holds no expressions; the others hold contexts or expressions of
  -- the elaboration)
  unless term1.letRecsToLift.isEmpty &&
      term1.syntheticMVars.toList.all (·.2.kind matches .typeClass _) do
    return .error s!"unsolved elaboration problems \
      ({term1.syntheticMVars.toList.map fun (id, d) =>
        s!"{d.kind} {mctx.eAssignment.contains id}"})"
  unless mctx.dAssignment.isEmpty && mctx.decls.toList.all (mctx.eAssignment.contains ·.1) do
    return .error "unassigned metavariables"
  unless xs.all (·.isFVar) do
    return .error "metavariables among the variables"
  let ctx := comps quotCtx
  let renames ← match unsafe renames? (ofCtx ctx) lctx meta1 core1.cache term1.levelNames with
    | .ok r => pure r
    | .error why => return .error why
  return .ok {
    start, deps, moduleUses, ngenPrefix := core0.ngen.namePrefix, ngenEnd := core1.ngen.idx
    names := core1.ngen.idx - core0.ngen.idx
    macroScopes := core1.nextMacroScope - core0.nextMacroScope
    quotCtx, renames, recDepth := ← MonadRecDepth.getRecDepth
    autoCtx := (← read).autoBoundImplicitContext
    autoImplicit := autoImplicit.get start.opts, lctx, localInsts := ← getLocalInstances, xs
    sectionFVars
    metaState := meta1, termState := term1, coreCache := core1.cache
    infoAssignment := core1.infoState.assignment, infoTrees := core1.infoState.trees, pos }

/--
Elaborates the section variables with `elabVars` (Lean's elaboration in `runTermElabM`, which passes
the variables and the map from their unique names to them to its continuation) and continues with
`k`, or sets the state that an earlier elaboration of the same section variables ended with, if
that elaboration would give it now, and continues with `k` in the context in which `elabVars` calls
`k` (that of `withAutoBoundImplicit`, `universeConstraintsCheckpoint`, the variables' local
context).
-/
def withSectionVars (varDecls : Array Syntax) (varUIds : Array Name) (opts : Options)
    (elabVars : ∀ {β}, (Array Expr → NameMap Expr → TermElabM β) → TermElabM β)
    (k : Array Expr → NameMap Expr → TermElabM α) : TermElabM α := do
  let env ← getEnv
  -- (`nativeAvailable` first: the stage0 `lean` that builds stage1 has none of this module's state)
  unless nativeAvailable env && Speculation.reuse do
    return (← elabVars k)
  if varDecls.isEmpty then
    return (← elabVars k)
  -- (the reuse's own work counts no heartbeats)
  let heartbeats ← IO.getNumHeartbeats
  let onThread ← Speculation.onElabThread
  let excluded? : Option Speculation.Exclusion :=
    if !onThread then some 7
    else if !reusableUnder opts then some 8
    else if env.asyncPrefix?.isSome then some 9
    else none
  if let some kind := excluded? then
    noteExcluded kind
    setHeartbeats heartbeats
    return (← elabVars k)
  let some start ← start? varDecls varUIds |
    noteExcluded 10
    setHeartbeats heartbeats
    return (← elabVars k)
  let ns ← getCurrNamespace
  let openDecls ← getOpenDecls
  let some entries ← takeEntries 1 #[] |
    noteExcluded 7
    setHeartbeats heartbeats
    return (← elabVars k)
  putEntries 1 entries
  let candidates := entries.filter (·.start.same start)
  let fileMap ← getFileMap
  let pos := s!"{(← getRef).getPos?.map fun p => fileMap.toPosition p}"
  let core0 ← getThe Core.State
  let meta0 ← getThe Meta.State
  let quotCtx ← MonadQuotation.getContext
  let mut failure? := none
  for e in candidates do
    if let some a := e.deps.firstFailure? env ns openDecls then
      if debugReuse then
        IO.eprintln s!"PaperLean: {pos}: section variables of {e.pos} not reused: \
          {EnvDeps.describe env a}"
      failure? := failure? <|> some a
      continue
    unless hasModuleUses env e.moduleUses do
      noteReason "not reused: a module use that is not there"
      continue
    unless core0.ngen.namePrefix == e.ngenPrefix && e.ngenEnd ≤ core0.ngen.idx do
      noteReason "not reused: another name generator"
      continue
    let (lctx, metaState) := unsafe renamed Speculation.fault e quotCtx
    -- (no entries of the caches of `isDefEq`, which Lean empties before each use anyway)
    let metaState := { metaState with
      cache := { metaState.cache with defEqTrans := {}, defEqPerm := {} } }
    let r := unsafe remapped e lctx metaState core0.ngen.idx
    if Speculation.reuseOracle then
      unsafe oracle e r elabVars
    if debugReuse then
      IO.eprintln s!"PaperLean: {pos}: section variables of {e.pos} reused \
        ({e.deps.checks.size} checks)"
    statsRef.modify fun (r, n, f) => (r + 1, n, f)
    -- (a recording that this elaboration is part of depends on what the reused one read)
    envRecordAll e.deps.accesses (unsafe unsafeCast e.deps.checks)
    set r.termState
    modifyThe Meta.State fun _ => r.metaState
    modifyThe Core.State fun s => { s with
      ngen.idx := s.ngen.idx + e.names, nextMacroScope := s.nextMacroScope + e.macroScopes
      cache := e.coreCache, messages := {}
      infoState := { s.infoState with assignment := r.infoAssignment, trees := r.infoTrees } }
    setHeartbeats heartbeats
    let body := universeConstraintsCheckpoint <| withLCtx r.lctx r.localInsts <| k r.xs r.sectionFVars
    return (← MonadRecDepth.withRecDepth (start.recDepth + (e.recDepth - e.start.recDepth)) <|
      withReader ({ · with autoBoundImplicitContext := r.autoCtx }) <|
        if e.autoImplicit then withSaveAutoImplicitInfoContext body else body)
  statsRef.modify fun (r, n, f) => (r, n + 1, if candidates.isEmpty then f else f + 1)
  -- (one reason for each elaboration, as for the numbers of `stats`; the first of a scope has none)
  if let some a := failure? then
    noteReason s!"not reused: {EnvDeps.reason env a}"
  if candidates.isEmpty then
    if let some e := entries.find? (·.start.varUIds == varUIds) then
      noteReason s!"not reused: another start ({e.start.difference start})"
      if debugReuse then
        IO.eprintln s!"PaperLean: {pos}: section variables of {e.pos} not reused: another start \
          ({e.start.difference start})"
  if let some (_, _, _, why) := (← unrecordableRef.get).find? fun (d, u, o, _) =>
      u == varUIds && o == opts && d == varDecls then
    noteReason s!"not kept: {why}"
    setHeartbeats heartbeats
    return (← elabVars k)
  let moduleUses := SectionVars.moduleUses env
  let rec_ ← EnvDeps.start
  setHeartbeats heartbeats
  tryFinally
    (elabVars fun xs sectionFVars => do
      let heartbeats ← IO.getNumHeartbeats
      let deps? ← rec_.stop
      match ← entry? start core0 meta0 moduleUses quotCtx deps? xs sectionFVars pos with
      | .ok e =>
        -- (entries for the same binders are kept too: their dependencies may hold at other
        -- times, e.g. in another namespace)
        if let some es ← takeEntries 1 #[] then
          putEntries 1 ((#[e] ++ es).take maxEntries)
      | .error why =>
        if debugReuse then
          IO.eprintln s!"PaperLean: {pos}: section variables not kept: {why}"
        noteReason s!"not kept: {why}"
        -- (but for a change of the environment, e.g. a module use recorded for the first time,
        -- the same binders give the same)
        unless why == "a change of the environment" do
          unrecordableRef.modify fun us => (#[(varDecls, varUIds, opts, why)] ++ us).take maxEntries
      setHeartbeats heartbeats
      k xs sectionFVars)
    -- (ending the recording counts no heartbeats, also on an exception)
    (do
      let heartbeats ← IO.getNumHeartbeats
      discard rec_.stop
      setHeartbeats heartbeats)

/-- With `PAPERLEAN_REUSE_STATS` set, appends the reuse of typeclass results and of section variables
of the module `fileName` to that file, to measure them over a build. -/
@[noinline] def writeReuseStats (fileName : String) : IO Unit := do
  if let some log ← IO.getEnv "PAPERLEAN_REUSE_STATS" then
    let (r, n, f) ← TCCache.stats
    let (sr, sn, sf) ← stats
    IO.FS.withFile log .append (·.putStrLn s!"{fileName}\t{r}\t{n}\t{f}\t\
      {" | ".intercalate (← TCCache.reasons)}\t{sr}\t{sn}\t{sf}\t\
      {" | ".intercalate (← SectionVars.reasons)}")

end Lean.PaperLean.SectionVars
