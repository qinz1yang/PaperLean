/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lean.Meta.Basic
public import Lean.Meta.AbstractMVars
public import Lean.Meta.Instances
public import Lean.PaperLean.EnvDeps
import all Lean.PaperLean.EnvDeps
public import Lean.PaperLean.Speculation
import Init.While
import all Init.System.CancelToken
import all Lean.Meta.Basic
import Lean.Util.CollectFVars
import Lean.Meta.FunInfo

-- (no `SizeOf` instances for PaperLean's types: an instance of a module of `Lean` would be one of
-- every environment that imports it, which Lean's searches would try)
set_option genSizeOf false
set_option genInjectivity false

public section

/-!
Typeclass results reused across the commands of a module (`Meta.synthInstanceCore?`), by `lean` on
the command line when a `paperlean` command asks for it (`Speculation.reuse`).

Lean caches typeclass results within a command (`Meta.Cache.synthInstance`) and solves the same
problems again in each later command, which in Mathlib is a large part of the time of theorem
headers. Here the result of Lean's search (`SynthInstance.main`) for a problem is kept with the
problem up to the renaming of free variables and metavariables (the free variables that the problem
and the local instances reach, closed under their types and values, numbered in local-context
order, with their types and values as they are and the values and types of the assigned
metavariables in these) and with every access to the environment that the search made
(`Lean.PaperLean.EnvDeps`). A later command with the same problem, options, configuration (also
whether `inferType` uses its cache) and visibility (`Environment.isExporting`) takes that result,
with its own free variables, if every access gives the same answer in its environment; the rest of
`synthInstanceCore?` (checking and applying the result, Lean's own cache) runs as for a result that
Lean's search found. Otherwise the search runs as Lean's.

A reuse gives the result of Lean's search and puts into Lean's caches only entries that Lean's
search puts there, keys and values alike; the caches may lack entries that Lean's search adds, of
which a later recomputation takes no names (they mention names that the search made, which no lookup
finds, or they are `inferType` of pure keys or transient entries of `isDefEq`; the numbering of names
reaches the environment, and the oracle compares it). The search's effects on the state are kept with
its result:
the names it took from the name generator (a reuse advances the generator by as many) and its
operations on Lean's caches of `MetaM` (`CacheOp`, recorded by Lean's functions that use the caches,
`PaperLean.noteCache`). A reuse requires each lookup of the search in these caches to find what it
found (the search's path, hence its result and its insertions, depends on them), and repeats its
insertions. Not so for the keys whose value Lean computes from the key alone (`pureKey`: `funInfo`
of imported constants, which `realizeValue` computes once for the module, and `inferType` of
imported constants and of their applications that need no `whnf`), where a hit and a miss give the
same value and Lean's search makes the same other operations either way: a miss of Lean's search is
repeated for `funInfo` (`fill`) and left out for `inferType`, and a hit makes none of the operations
of the computation that the recorded search made instead. It leaves out the operations on entries
that mention a name that the search made, and leaves those of `CoreM` for instantiating universe
parameters as they are, whose hits give what misses compute (so the search's path does not depend on
them). The caches of `isDefEq` are emptied at the start of each `isDefEq`, so that the search's path
does not depend on them either, but an `isDefEq` that the search runs in goes on using what the search
left there. After a search that found something, `assignOutParams` runs an `isDefEq`, for a reuse too,
which empties them whatever the search did. After one that found nothing, a reuse leaves them as the
search did (`DefEqEffect`, `DefEqEffect.apply`): empty where the search emptied them, as it may not
have (without an instance to try, it runs no `isDefEq`; a universe `isDefEq` empties only the transient
cache), with the search's entries of the permanent cache. Its entries of the transient cache
mention names that the search made or no metavariable at all, which no lookup there finds. The
search must leave the rest of the state as it was (the environment, the metavariable context,
messages, the counter of macro scopes, ...), and the caches as its recorded operations make them;
otherwise it is not kept. A search whose result, operations on the caches (keys or values) or entries
of the permanent cache of `isDefEq` mention a binder name with macro scopes of the problem (names that
differ from command to command) is reused only for the same names. A search whose problem holds
syntax in metadata is not kept, as a key does not compare its positions. What is kept is worked out
when a later problem first has the key of the search (`finished`), as about half of the searches
never see theirs again. A search of fewer heartbeats than `minHeartbeats` is not kept, as its reuse
would cost about as much, and the next search with its key runs as Lean's, without being recorded.

Only the threads that elaborate commands in order use the cache (`Speculation.onElabThread`; not the
tasks that they start, e.g. of linters, nor the elaboration of declarations in the background), and
only for problems without metavariables in them, but in output parameters (which the search replaces),
and without unassigned (or delayed-assigned) ones in the context they reach, whose assigned ones
have values without metavariables, and whose context is small (`maxDecls`, `maxContext`); not with
trace options or diagnostics, nor under a custom
unfolding predicate, let-variables to unfold (`Meta.Context.zetaDeltaSet`), the tracking of
unfolded let-variables (a side effect that a reuse would not repeat), or the name generator of
`grind`'s theorem instantiation. The search reads the instance index only for the classes of its
goals, and its dependency is on those
(`getInstancesUnify`). The cache's own work counts no heartbeats. With `PAPERLEAN_REUSE_ORACLE` set
(for testing), each reuse is compared with Lean's search from the same state, which reuses nothing
(its result, the state it leaves, and the entries that the reuse inserts), and `lean` fails if they
differ (`Lean.PaperLean.Speculation`).
-/

namespace Lean.PaperLean.TCCache
open Meta

/-! The instances that a search reads, as recorded (`Lean.PaperLean.EnvDeps`). -/

/-- The state of the instances, not recorded. -/
private def instancesUnrecorded (env : Environment) : Instances :=
  envWithoutRecording fun _ => instanceExtension.getState env

private unsafe def sameObj? {α : Type} (a b : Option α) : Bool :=
  match a, b with
  | some x, some y => ptrEq x y
  | none, none => true
  | _, _ => false

/-- Whether the erased instances `a` and `b` have the same members: `addInstanceEntry` copies an
erased set that has subnodes for every instance added. -/
private unsafe def sameErased (a b : PHashSet Name) : Bool :=
  ptrEq a b ||
    a.fold (fun ok n => ok && b.contains n) true && b.fold (fun ok n => ok && a.contains n) true

/-- `result`, after recording the parts of the instances `s` under which the lookup of a goal with
root key `key` looked. -/
private unsafe def recordInstances (s : Instances) (key : DiscrTree.Key)
    (result : Array InstanceEntry) (_ _ : Unit) : Array InstanceEntry :=
  let idx := instanceExtension.ext.toEnvExtension.idx
  match key with
  | .const c n =>
    let trie? := s.discrTree.root.find? key
    let star? := s.discrTree.root.find? .star
    let erased := s.erased
    envRecord (.extPart idx (.num c n)) (unsafeCast
      fun (env' : Environment) (_ : Name) (_ : NonScalar) =>
        let s' := instancesUnrecorded env'
        sameObj? (s'.discrTree.root.find? key) trie? &&
          sameObj? (s'.discrTree.root.find? .star) star? && sameErased s'.erased erased) result
  -- (a goal whose root key is `.star` unifies with the instances under every key: as
  -- `ScopedEnvExtension.getState` records it)
  | _ =>
    envRecord (.ext idx 100 .anonymous) (unsafeCast
      fun (env' : Environment) (_ : Name) (_ : NonScalar) =>
        ptrEq (instancesUnrecorded env') s) result

private unsafe def getInstancesUnifyImpl (type : Expr) : MetaM (Array InstanceEntry) := do
  -- (counting no heartbeats, as the root key is looked up again)
  let heartbeats ← IO.getNumHeartbeats
  let s := instancesUnrecorded (← getEnv)
  let result ← s.discrTree.getUnify type
  let key ← DiscrTree.getUnifyRootKey type
  let result := uncounted5 recordInstances s key result () ()
  setHeartbeats heartbeats
  return result

/--
`(← getGlobalInstancesIndex).getUnify type` while this thread records, which records only what the
result depends on: the entries of the instance index under the root key of `type` and under
`.star`, and the erased instances, which `SynthInstance.getInstances` reads too
(`erasedInstancesUnrecorded`). An instance of another class leaves these the same objects.
-/
@[implemented_by getInstancesUnifyImpl]
opaque getInstancesUnify (type : Expr) : MetaM (Array InstanceEntry)

/-- `getErasedInstances`, which `getInstancesUnify` records (counting no heartbeats). -/
def erasedInstancesUnrecorded : CoreM (PHashSet Name) :=
  return uncounted5 (fun env _ _ _ _ => (instancesUnrecorded env).erased) (← getEnv) () () () ()

/-- An expression compared with `EnvDeps.sameExpr`, which also compares binder annotations (`BEq
Expr` does not; a local instance's binder annotations decide the subgoals of the search), and
binder names up to macro scopes. -/
structure ExactExpr where
  expr : Expr

-- (the instances of PaperLean's types are local: an instance of a module of `Lean` would be one of
-- every environment that imports it, which Lean's searches would try)
local instance : BEq ExactExpr where
  -- (`Expr.equal` implies `sameExpr`)
  beq a b := a.expr.equal b.expr || EnvDeps.sameExpr a.expr b.expr

local instance : Hashable ExactExpr where
  hash e := hash e.expr

/-- A typeclass problem up to the renaming of free variables, which are replaced by `canonFVar`. -/
structure Key where
  /-- The hash of the other fields, compared first. -/
  hash : UInt64
  type : ExactExpr
  /-- The types, values and kinds of the free variables that the problem reaches, in local-context
  order, as they are (the search sees them so), with their assigned metavariables and universe
  metavariables replaced by their numbers in `mvars` and `lmvars` (`canonRaw`). -/
  decls : Array (ExactExpr × Option ExactExpr × LocalDeclKind)
  /-- The value and the type of each metavariable of `decls`. -/
  mvars : Array (ExactExpr × ExactExpr)
  /-- The value of each universe metavariable of `decls`. -/
  lmvars : Array Level
  /-- The class and the number of each local instance. -/
  localInsts : Array (Name × Nat)
  synthPendingDepth : Nat
  maxResultSize : Nat
  configKey : UInt64
  univApprox : Bool
  /-- `Meta.Context.cacheInferType`: whether `inferType` uses its cache (the search's operations on
  it). -/
  cacheInferType : Bool
  opts : Options
  /-- `Environment.isExporting`: whether private constants, e.g. instances, are visible. -/
  isExporting : Bool

local instance : BEq Key where
  beq a b := a.hash == b.hash && a.type == b.type && a.decls == b.decls && a.mvars == b.mvars &&
    a.lmvars == b.lmvars &&
    a.localInsts == b.localInsts && a.synthPendingDepth == b.synthPendingDepth &&
    a.maxResultSize == b.maxResultSize && a.configKey == b.configKey &&
    a.univApprox == b.univApprox && a.cacheInferType == b.cacheInferType && a.opts == b.opts &&
    a.isExporting == b.isExporting

local instance : Hashable Key where
  hash k := k.hash

/-- The expressions of `k`, for which `BEq Key` compares binder names up to macro scopes. -/
private def Key.exprs (k : Key) : Array Expr :=
  let es := k.decls.foldl (init := #[k.type.expr]) fun es (t, v?, _) =>
    match v? with
    | some v => es.push t.expr |>.push v.expr
    | none => es.push t.expr
  k.mvars.foldl (init := es) fun es (v, t) => es.push v.expr |>.push t.expr

/-- Whether `a` and `b`, equal keys, have the same binder names. -/
private def Key.sameNames (a b : Key) : Bool :=
  a.exprs.size == b.exprs.size && (a.exprs.zip b.exprs).all fun (x, y) => x.equal y

/-! Lean's caches of `MetaM` whose operations a search records (`PaperLean.noteCache`), numbered as
by the hooks: `inferType` 0, `funInfo` 1, `synthInstance` 2, `whnf` 3. -/

/-- An operation of a search on one of Lean's caches (numbered as above), as kept: keys and values
with the free variables of the problem replaced by `canonFVar`. -/
inductive CacheOp where
  /-- A lookup of `key` that found `found?`. -/
  | lookup (cache : UInt8) (key : NonScalar) (found? : Option NonScalar)
  /-- The insertion of `value` under `key`. -/
  | insert (cache : UInt8) (key value : NonScalar)
  /-- A lookup of `key`, a `pureKey`, that found `found?`; for one that found none, `insertAt?` is
  the index of the search's insertion under `key` if the operations up to it are on pure keys
  only. -/
  | pureLookup (cache : UInt8) (key : NonScalar) (found? : Option NonScalar)
      (insertAt? : Option Nat)

/-- The expressions of a key of cache `c`. -/
private unsafe def keyExprs (c : UInt8) (k : NonScalar) : Array Expr :=
  if c == 0 || c == 3 then #[(unsafeCast k : ExprConfigCacheKey).expr]
  else if c == 1 then #[(unsafeCast k : InfoCacheKey).expr]
  else
    let k : SynthInstanceCacheKey := unsafeCast k
    k.localInsts.map (·.fvar) |>.push k.type

/-- Whether an expression of a key of cache `c` satisfies `p` (`keyExprs`). -/
@[inline] private unsafe def keyAny (c : UInt8) (k : NonScalar) (p : Expr → Bool) : Bool :=
  if c == 0 || c == 3 then p (unsafeCast k : ExprConfigCacheKey).expr
  else if c == 1 then p (unsafeCast k : InfoCacheKey).expr
  else
    let k : SynthInstanceCacheKey := unsafeCast k
    k.localInsts.any (p ·.fvar) || p k.type

/-- The expressions of a value of cache `c`. -/
private unsafe def valueExprs (c : UInt8) (v : NonScalar) : Array Expr :=
  if c == 0 || c == 3 then #[unsafeCast v]
  else if c == 1 then #[]
  else match (unsafeCast v : Option AbstractMVarsResult) with
    | some r => r.mvars.push r.expr
    | none => #[]

/-- Whether an expression of a value of cache `c` satisfies `p` (`valueExprs`). -/
@[inline] private unsafe def valueAny (c : UInt8) (v : NonScalar) (p : Expr → Bool) : Bool :=
  if c == 0 || c == 3 then p (unsafeCast v)
  else if c == 1 then false
  else match (unsafeCast v : Option AbstractMVarsResult) with
    | some r => r.mvars.any p || p r.expr
    | none => false

/-- The value `v` of cache `c` with `f` applied to its expressions. -/
private unsafe def mapValue (c : UInt8) (f : Expr → Expr) (v : NonScalar) : NonScalar :=
  if !valueAny c v (·.hasFVar) then v
  else if c == 0 || c == 3 then unsafeCast (f (unsafeCast v))
  else unsafeCast ((unsafeCast v : Option AbstractMVarsResult).map fun r =>
    { r with mvars := r.mvars.map f, expr := f r.expr })

/-- Results of mapping expression roots within one fixed free-variable renaming. The pointer map
retains the input as its key, preventing address reuse. Never shared across calls. -/
private unsafe abbrev ExprRemapMemo := PtrMap Expr Expr

/-- The existing pure renaming `f`, memoized for roots shared by operations of one phase. Closed
roots need no renaming and do not enter the memo. The traversal also memoizes shared subterms. -/
private unsafe def remapExpr (f : Expr → Expr) (e : Expr) : StateM ExprRemapMemo Expr := do
  if !e.hasFVar then return e
  if let some result := PtrMap.find? (← get) e then return result
  let result := f e
  modify fun memo => PtrMap.insert memo e result
  return result

/-- The key `k` of cache `c` with `f` applied to its expressions, through the phase's root memo. -/
private unsafe def mapKeyMemo (c : UInt8) (f : Expr → Expr) (k : NonScalar) :
    StateM ExprRemapMemo NonScalar := do
  if !keyAny c k (·.hasFVar) then return k
  if c == 0 || c == 3 then
    let k : ExprConfigCacheKey := unsafeCast k
    return unsafeCast ({ k with expr := ← remapExpr f k.expr } : ExprConfigCacheKey)
  else if c == 1 then
    let k : InfoCacheKey := unsafeCast k
    return unsafeCast ({ k with expr := ← remapExpr f k.expr } : InfoCacheKey)
  else
    let k : SynthInstanceCacheKey := unsafeCast k
    return unsafeCast ({ k with
      localInsts := ← k.localInsts.mapM fun li => return { li with fvar := ← remapExpr f li.fvar }
      type := ← remapExpr f k.type } : SynthInstanceCacheKey)

/-- `mapValue` with the same phase-local root memo. -/
private unsafe def mapValueMemo (c : UInt8) (f : Expr → Expr) (v : NonScalar) :
    StateM ExprRemapMemo NonScalar := do
  if !valueAny c v (·.hasFVar) then return v
  if c == 0 || c == 3 then return unsafeCast (← remapExpr f (unsafeCast v))
  else
    let r? : Option AbstractMVarsResult := unsafeCast v
    let r? ← r?.mapM fun r => do
      return { r with mvars := ← r.mvars.mapM (remapExpr f), expr := ← remapExpr f r.expr }
    return unsafeCast r?

private unsafe def findIn (c : UInt8) (cache : Meta.Cache) (k : NonScalar) : Option NonScalar :=
  if c == 0 then unsafeCast (cache.inferType.find? (unsafeCast k))
  else if c == 1 then unsafeCast (cache.funInfo.find? (unsafeCast k))
  else if c == 2 then unsafeCast (cache.synthInstance.find? (unsafeCast k))
  else unsafeCast (cache.whnf.find? (unsafeCast k))

private unsafe def insertIn (c : UInt8) (cache : Meta.Cache) (k v : NonScalar) : Meta.Cache :=
  if c == 0 then { cache with inferType := cache.inferType.insert (unsafeCast k) (unsafeCast v) }
  else if c == 1 then { cache with funInfo := cache.funInfo.insert (unsafeCast k) (unsafeCast v) }
  else if c == 2 then
    { cache with synthInstance := cache.synthInstance.insert (unsafeCast k) (unsafeCast v) }
  else { cache with whnf := cache.whnf.insert (unsafeCast k) (unsafeCast v) }

private def sameParamInfo (a b : ParamInfo) : Bool :=
  a.binderInfo == b.binderInfo && a.hasFwdDeps == b.hasFwdDeps && a.backDeps == b.backDeps &&
    a.isProp == b.isProp && a.isDecInst == b.isDecInst && a.isInstance == b.isInstance &&
    a.higherOrderOutParam == b.higherOrderOutParam &&
    a.dependsOnHigherOrderOutParam == b.dependsOnHigherOrderOutParam

/-- Whether the values `a` and `b` of cache `c` are equal, binder names included. -/
private unsafe def sameValue (c : UInt8) (a b : NonScalar) : Bool :=
  ptrEq a b ||
  if c == 0 || c == 3 then (unsafeCast a : Expr).equal (unsafeCast b)
  else if c == 1 then
    let a : FunInfo := unsafeCast a
    let b : FunInfo := unsafeCast b
    a.resultDeps == b.resultDeps && a.paramInfo.size == b.paramInfo.size &&
      (a.paramInfo.zip b.paramInfo).all fun (x, y) => sameParamInfo x y
  else
    match (unsafeCast a : Option AbstractMVarsResult),
      (unsafeCast b : Option AbstractMVarsResult) with
    | some r, some s =>
      r.paramNames == s.paramNames && r.mvars.size == s.mvars.size &&
        (r.mvars.zip s.mvars).all (fun (x, y) => x.equal y) && r.expr.equal s.expr
    | none, none => true
    | _, _ => false

/-- The root of the map of cache `c`. -/
private unsafe def rootOf (c : UInt8) (cache : Meta.Cache) :
    PersistentHashMap.Node NonScalar NonScalar :=
  if c == 0 then unsafeCast cache.inferType.root
  else if c == 1 then unsafeCast cache.funInfo.root
  else if c == 2 then unsafeCast cache.synthInstance.root
  else unsafeCast cache.whnf.root

/-- The entries of the node `b` where it is not the node `a`, walking only where `b` is not `a`
(an insertion copies the nodes on the path to the entry and shares the others): `acc` with those. -/
private unsafe def changedEntries (a b : PersistentHashMap.Node NonScalar NonScalar)
    (acc : Array (NonScalar × NonScalar)) : Array (NonScalar × NonScalar) :=
  if ptrEq a b then acc else
  match a, b with
  | .entries ea, .entries eb => Id.run do
    let mut acc := acc
    for h : i in [0:eb.size] do
      let y := eb[i]
      let x := ea[i]?.getD .null
      if ptrEq x y then continue
      match x, y with
      | .ref na, .ref nb => acc := changedEntries na nb acc
      | _, .ref nb => acc := all nb acc
      | .entry k v, .entry k' v' => unless ptrEq k k' && ptrEq v v' do acc := acc.push (k', v')
      | _, .entry k' v' => acc := acc.push (k', v')
      | _, .null => pure ()
    return acc
  | _, _ => all b acc
where
  all (b : PersistentHashMap.Node NonScalar NonScalar) (acc : Array (NonScalar × NonScalar)) :
      Array (NonScalar × NonScalar) :=
    match b with
    | .entries es => es.foldl (init := acc) fun acc e =>
      match e with
      | .entry k v => acc.push (k, v)
      | .ref n => all n acc
      | .null => acc
    | .collision ks vs _ => (ks.zip vs).foldl (init := acc) fun acc kv => acc.push kv

/-- Whether the caches `cache1` (after a search) are `sim` (those before it, `cache0`, with the
search's recorded insertions): each entry of `cache1` where its maps are not those of `cache0` is
one of `cache0` or one that `sim` has, and each entry of `cache0` where they differ is in
`cache1`. -/
private unsafe def madeByInsertions (cache0 sim cache1 : Meta.Cache) : Bool :=
  [(0 : UInt8), 1, 2, 3].all fun c =>
    (changedEntries (rootOf c cache0) (rootOf c cache1) #[]).all (fun (k, v) =>
      sameObj? (findIn c cache0 k) (some v) || sameObj? (findIn c sim k) (some v)) &&
    (changedEntries (rootOf c cache1) (rootOf c cache0) #[]).all fun (k, _) =>
      (findIn c cache1 k).isSome

/-- What a search that found nothing did to the caches of `isDefEq`. -/
structure DefEqEffect where
  /-- Whether it emptied the transient cache. -/
  emptiesTrans : Bool := false
  /-- Whether it emptied the permanent cache. -/
  emptiesPerm : Bool := false
  /-- If so, what it left there, but for entries that mention a name that it made, with the free
  variables of the problem replaced by `canonFVar`. -/
  perm : Array (DefEqCacheKey × Bool) := #[]

/-- A result of Lean's search with what it depended on and what it changed. -/
structure Entry where
  /-- The problem, as recorded (binder names included). -/
  key : Key
  deps : EnvDeps.Deps
  /-- The result, with free variables replaced by `canonFVar`. -/
  result : Option AbstractMVarsResult
  /-- The number of names that the search took from the name generator, by which a reuse advances
  it. -/
  names : Nat
  /-- The search's operations on Lean's caches that a reuse checks or repeats, in order. -/
  ops : Array CacheOp
  /-- Whether replay can need to fill a missing `funInfo` entry. Computed once from `ops`, so an
  unrecorded replay without fills or an oracle need not build an unused trace of its operations. -/
  mayFill : Bool
  /-- For a search that found nothing, what a reuse repeats on the caches of `isDefEq`. -/
  defEq : DefEqEffect
  /-- Whether the result, the keys and values in `ops` and the keys in `defEq.perm` mention no binder
  name with macro scopes of the problem: otherwise the entry is reused only for a problem with the same
  binder names. -/
  namesFree : Bool

/-- A search as it ended, of which `finished` makes an `Entry` when a later problem first has its key:
about half of the searches never see their key again. -/
structure Pending where
  key : Key
  fvars : Array FVarId
  result : Option AbstractMVarsResult
  raw : EnvDeps.Raw
  /-- The name generator before the search, and its index after it. -/
  ngen0 : NameGenerator
  ngenEnd : Nat
  /-- Whether the search emptied the transient and the permanent cache of `isDefEq` (`mark`), and what
  the latter held after it, if the search found nothing and emptied it. -/
  emptiedTrans : Bool
  emptiedPerm : Bool
  perm : DefEqCache

/-- What is kept of a search. -/
inductive Stored where
  | pending (p : Pending)
  | entry (e : Entry)
  /-- The last search of the key cost fewer heartbeats than `minHeartbeats`: the next one is not
  recorded. -/
  | cheap

/-- Counts of retained records and a weighted reference-slot charge, not transitive heap bytes:
expressions and check closures can share or retain larger graphs. The limits bound this charge; the byte
benefit and the cost of counting permanent-cache entries require workload measurements. -/
private structure RetentionCount where
  keys : Nat := 0
  pending : Nat := 0
  entries : Nat := 0
  cheap : Nat := 0
  slots : Nat := 0
  operations : Nat := 0

private def RetentionCount.add (a b : RetentionCount) : RetentionCount :=
  ⟨a.keys + b.keys, a.pending + b.pending, a.entries + b.entries, a.cheap + b.cheap,
   a.slots + b.slots, a.operations + b.operations⟩

private def RetentionCount.sub (a b : RetentionCount) : RetentionCount :=
  ⟨a.keys - b.keys, a.pending - b.pending, a.entries - b.entries, a.cheap - b.cheap,
   a.slots - b.slots, a.operations - b.operations⟩

/-- Per-generation bounds. Two generations retain at most twice either limit. The overrides and
unbounded switch are for comparing the same executable; they do not change recording admission
or the 1024-heartbeat default. -/
private builtin_initialize retentionKeys : Nat ←
  return ((← IO.getEnv "PAPERLEAN_TC_CACHE_KEYS").bind String.toNat?).getD 4096
private builtin_initialize retentionSlots : Nat ←
  return ((← IO.getEnv "PAPERLEAN_TC_CACHE_SLOTS").bind String.toNat?).getD 524288
private builtin_initialize retentionUnbounded : Bool ←
  return (← IO.getEnv "PAPERLEAN_TC_CACHE_UNBOUNDED").isSome
private builtin_initialize retentionDiagnostics : Bool ←
  return (← IO.getEnv "PAPERLEAN_REUSE_STATS").isSome

private def retainedCount (key : Key) (stored : Array Stored) : RetentionCount := Id.run do
  let keySlots (k : Key) := 1 + 2 * k.decls.size + 2 * k.mvars.size + k.lmvars.size + k.localInsts.size
  let mut n : RetentionCount := { keys := 1, slots := keySlots key }
  let resultSlots (r : Option AbstractMVarsResult) :=
    r.map (fun r => 1 + r.mvars.size + r.paramNames.size) |>.getD 0
  for s in stored do
    match s with
    | .cheap => n := { n with cheap := n.cheap + 1, slots := n.slots + 1 }
    | .pending p =>
      -- Only a failed search that emptied the permanent cache retained a map.
      let perm := if p.result.isSome || !p.emptiedPerm then 0 else
        p.perm.foldl (fun n _ _ => n + 1) 0
      let ops := if retentionDiagnostics then
          p.raw.accesses.foldl (fun n a => if a matches .cache .. then n + 1 else n) 0
        else 0
      n := { n with
        pending := n.pending + 1
        slots := n.slots + 1 + keySlots p.key + p.fvars.size + resultSlots p.result +
          3 * p.raw.accesses.size + p.raw.checks.size + 2 * perm
        operations := n.operations + ops }
    | .entry e =>
      n := { n with
        entries := n.entries + 1
        slots := n.slots + 1 + keySlots e.key + resultSlots e.result + 3 * e.deps.accesses.size + e.deps.checks.size +
          3 * e.deps.cacheOps.size + 3 * e.ops.size + 2 * e.defEq.perm.size
        operations := n.operations + e.ops.size }
  return n

private structure Retained where
  stored : Array Stored
  count : RetentionCount
  /-- Lookup clock at the last replacement; used only with reuse statistics enabled. -/
  born : Nat

private abbrev EntryMap := PersistentHashMap Key Retained

/-- Recently inserted/looked-up keys and the preceding generation. A lookup promotes an older key;
when the recent generation fills, the older one is discarded and the recent one becomes older.
There is no growing FIFO of stale key references. Hits in the recent generation do not rewrite its
map. Eviction only loses an optimization opportunity: the ordinary search remains the fallback. -/
private structure Entries where
  recent : EntryMap := {}
  older : EntryMap := {}
  recentCount : RetentionCount := {}
  olderCount : RetentionCount := {}
  clock : Nat := 0
  keyHits : Nat := 0
  ageSum : Nat := 0
  ageMax : Nat := 0
  evictedKeys : Nat := 0
  oversized : Nat := 0
  peakKeys : Nat := 0
  peakSlots : Nat := 0

private def Entries.erase (s : Entries) (key : Key) : Entries := Id.run do
  let mut s := s
  if let some r := s.recent.find? key then
    s := { s with recent := s.recent.erase key, recentCount := s.recentCount.sub r.count }
  if let some r := s.older.find? key then
    s := { s with older := s.older.erase key, olderCount := s.olderCount.sub r.count }
  return s

private def Entries.insertRetained (s : Entries) (key : Key) (r : Retained) : Entries := Id.run do
  let mut s := s.erase key
  if !retentionUnbounded && (retentionKeys == 0 || r.count.slots > retentionSlots) then
    return { s with oversized := s.oversized + 1 }
  if !retentionUnbounded &&
      (s.recentCount.keys + 1 > retentionKeys || s.recentCount.slots + r.count.slots > retentionSlots) then
    s := { s with
      older := s.recent, olderCount := s.recentCount, recent := {}, recentCount := {}
      evictedKeys := s.evictedKeys + s.olderCount.keys }
  s := { s with recent := s.recent.insert key r, recentCount := s.recentCount.add r.count }
  return { s with
    peakKeys := max s.peakKeys (s.recentCount.keys + s.olderCount.keys)
    peakSlots := max s.peakSlots (s.recentCount.slots + s.olderCount.slots) }

private def Entries.insert (s : Entries) (key : Key) (stored : Array Stored) : Entries :=
  if stored.isEmpty then s.erase key else
    s.insertRetained key ⟨stored, retainedCount key stored, s.clock⟩

private def Entries.find (s : Entries) (key : Key) : (Key × Array Stored) × Entries := Id.run do
  let mut s := if retentionDiagnostics then { s with clock := s.clock + 1 } else s
  let found := match s.recent.findEntry? key with
    | some r => some (r, false)
    | none => s.older.findEntry? key |>.map (·, true)
  let some ((key, r), promote) := found | return ((key, #[]), s)
  if retentionDiagnostics then
    let age := s.clock - r.born
    s := { s with keyHits := s.keyHits + 1, ageSum := s.ageSum + age, ageMax := max s.ageMax age }
  if promote then s := s.insertRetained key r
  return ((key, r.stored), s)

/-- The entries (`empty` if none were put yet), out of the native store where they are kept,
which leaves it taken; none if it is taken, which turns reuse off. Unlike a global reference,
the entries and the objects they share with Lean's caches and terms are not marked multi-threaded.
The private retention store uses the same opaque native slot, without a serialized layout change. -/
@[extern "lean_paperlean_take_store"]
private opaque takeEntries (slot : UInt8) (empty : Entries) : BaseIO (Option Entries)
/-- Puts `m` into the native store of the entries, which `takeEntries` left taken. -/
@[extern "lean_paperlean_put_store"]
private opaque putEntries (slot : UInt8) (m : Entries) : BaseIO Unit

/-- Only the selected records escape this call, so a running search does not retain a snapshot of
both complete generations while nested searches rotate or replace the store.

One thread at a time uses the stores of reuse (also `SectionVars.takeEntries`) and their objects,
which are not marked multi-threaded, so a use needs to hold no store. Only threads on which
`Speculation.onElabThread` holds use them: in `doElab` of `Language.Lean.process`, for the one
frontend of the process that reuses, the first, of the command-line `lean`; any other frontend turns
reuse off before it elaborates (`Speculation.noteFrontend`). That frontend elaborates its commands
one after another, each once the one before has returned, in the same task or one chained after it.
The tasks that a command starts run on other threads, not marked as ones of reuse; a thread that
waits for a task does not run another one; what a thread hands to another (a task's closure, a
promise's value, a reference's value) is marked multi-threaded first, by that thread. The take and
the put of the store also see a second thread at once, which would be a defect, and turn reuse
off. -/
private def getStored? (key : Key) : BaseIO (Option (Key × Array Stored)) := do
  let some s ← takeEntries 0 {} | return none
  let (found, s) := s.find key
  putEntries 0 s
  return some found

private def modifyEntries (f : Entries → Entries) : BaseIO Unit := do
  if let some s ← takeEntries 0 {} then putEntries 0 (f s)

private def retentionReport : BaseIO String := do
  let some s ← takeEntries 0 {} | return "retention unavailable"
  let n := s.recentCount.add s.olderCount
  let report := s!"retention keys={n.keys} pending={n.pending} entries={n.entries} cheap={n.cheap} \
    slots={n.slots} operations={n.operations} peakKeys={s.peakKeys} peakSlots={s.peakSlots} \
    evictedKeys={s.evictedKeys} oversized={s.oversized} keyHits={s.keyHits} \
    hitAgeSum={s.ageSum} hitAgeMax={s.ageMax}"
  putEntries 0 s
  return report

/-- Reused, searched (cache missed), and searched because an entry's dependencies did not hold. -/
private builtin_initialize statsRef : IO.Ref (Nat × Nat × Nat) ← IO.mkRef (0, 0, 0)

/-- Why searches were not kept, or entries not reused, with their numbers. -/
private builtin_initialize reasonsRef : Speculation.Reasons ← IO.mkRef {}

/-- The numbers of typeclass problems of this process whose result was reused, searched, and
searched because an earlier search's dependencies or cache lookups did not hold. -/
def stats : BaseIO (Nat × Nat × Nat) := statsRef.get

/-- Why searches of this process were not kept, entries not reused, or searches left out
(`Speculation.Reasons.render`). -/
def reasons : BaseIO (List String) := do
  let reasons := (← reasonsRef.render) ++ (← Speculation.renderExclusions true)
  if retentionDiagnostics then return reasons ++ [← retentionReport]
  return reasons

/-- The position of `ref` in the file, as `line:column`. -/
def posOf (fileMap : FileMap) (ref : Syntax) : String :=
  let p := fileMap.toPosition (ref.getPos?.getD 0)
  s!"{p.line}:{p.column}"

private def noteReason (why : String) : MetaM Unit := do
  let (fileMap, ref) := (← getFileMap, ← getRef)
  reasonsRef.note why fun _ => posOf fileMap ref

/-- Counts a search left out of reuse in the way `kind`, on any thread. -/
@[noinline] def noteExcluded (kind : Speculation.Exclusion) : MetaM Unit := do
  let (fileMap, ref) := (← getFileMap, ← getRef)
  Speculation.noteExclusion kind fun _ => posOf fileMap ref

private def maxEntriesPerKey := 4

/-- The fewest heartbeats of a search that is kept (`PAPERLEAN_REUSE_MIN_HEARTBEATS` sets another, for
testing). A reuse (its lookup, checks and replay) costs about what a search of this many heartbeats
does, and recording a search slows it down by about a fifth. -/
private builtin_initialize minHeartbeats : Nat ← do
  return ((← IO.getEnv "PAPERLEAN_REUSE_MIN_HEARTBEATS").bind String.toNat?).getD 1024

/-- The `i`-th free variable of a problem, in `Key` and `Entry`. -/
private def canonFVar (i : Nat) : Expr :=
  .fvar ⟨.num `_paperlean_tc i⟩

/-- The prefix of the name generator of `grind`'s theorem instantiation, which starts again each time,
so that a later search makes the names of an earlier one (`keptOps` takes those for new). -/
private def grindNamePrefix : Name := `_uniq.grind.ematch

/-- Whether this command may use the cache, under the options `opts`: on the command line, and not
with trace options or diagnostics, whose output reflects the search. -/
private def usableUnder (opts : Options) : Bool := Id.run do
  if !internal.cmdlineSnapshots.get opts || opts.getBool `diagnostics then
    return false
  for (n, v) in opts do
    if n.getRoot == `trace && v matches .ofBool true then
      return false
  return true

/-- The free variable that `SynthInstance.preprocess` puts in the output parameters of a problem's
`cacheKeyType`, which is no variable of the context. -/
private def wildcardFVarId : FVarId := { name := `__wild__ }

/-- `e` with its assigned metavariables instantiated in `mctx`, unless some remain, and `mctx` with
the assignments that this instantiated (so that later instantiations share the terms). -/
private def instantiated? (mctx : MetavarContext) (e : Expr) : Option Expr × MetavarContext :=
  if !e.hasMVar then
    (some e, mctx)
  else
    let (e, mctx) := instantiateMVarsCore mctx e
    (if e.hasMVar then none else some e, mctx)

/-- The metavariables and universe metavariables met by `canonRaw`, in order, with their numbers,
and its cache. -/
private structure RawCanon where
  mvars : Array MVarId := #[]
  mvarNums : Std.HashMap MVarId Nat := {}
  lmvars : Array LMVarId := #[]
  lmvarNums : Std.HashMap LMVarId Nat := {}
  cache : Std.HashMap USize Expr := {}
  levelCache : Std.HashMap USize Level := {}

/-- The monad of `canonRaw`, which fails with the exclusion of the problem
(`Speculation.Exclusion`). -/
private abbrev KeyM := StateT RawCanon (Except Speculation.Exclusion)

/-- The universe level `u` of a problem's context with its assigned universe metavariables replaced
by their numbers (`RawCanon.lmvars`), if each is assigned a level without metavariables. -/
private unsafe def canonRawLevel (mctx : MetavarContext) (u : Level) : KeyM Level := do
  if !u.hasMVar then return u
  let key := ptrAddrUnsafe u
  if let some r := (← get).levelCache[key]? then return r
  let r ← match u with
    | .mvar id => do
      let some v := mctx.lAssignment.find? id | throw 4
      if v.hasMVar then throw 4
      let s ← get
      let i := s.lmvarNums.getD id s.lmvars.size
      if i == s.lmvars.size then
        set { s with lmvars := s.lmvars.push id, lmvarNums := s.lmvarNums.insert id i }
      pure <| .mvar ⟨.num `_paperlean_lmv i⟩
    | .succ v => pure (u.updateSucc! (← canonRawLevel mctx v))
    | .max a b => pure (u.updateMax! (← canonRawLevel mctx a) (← canonRawLevel mctx b))
    | .imax a b => pure (u.updateIMax! (← canonRawLevel mctx a) (← canonRawLevel mctx b))
    | _ => pure u
  modify fun s => { s with levelCache := s.levelCache.insert key r }
  return r

/-- `e`, a type or value of a problem's context as it is, with the free variables `num` replaced by
their numbers and its assigned metavariables and universe metavariables by their numbers
(`RawCanon`), if each is assigned a value without metavariables and none is delayed-assigned, and
there are at most `maxMVars` of them: the search sees the context so, and where a metavariable is
decides its steps (e.g. a term with one is not cached). -/
private unsafe def canonRaw (mctx : MetavarContext) (num : Std.HashMap FVarId Nat) (maxMVars : Nat)
    (e : Expr) : KeyM Expr := do
  if !e.hasFVar && !e.hasMVar then return e
  let k := ptrAddrUnsafe e
  if let some r := (← get).cache[k]? then return r
  -- (`pure`, not `return`, in each case: the result is cached, so that the term keeps its sharing)
  let r ← match e with
    | .fvar id =>
      if id == wildcardFVarId then pure e else
      let some i := num[id]? | throw 4
      pure (canonFVar i)
    | .mvar id => do
      let some v := mctx.getExprAssignmentCore? id | throw 4
      if v.hasMVar || mctx.dAssignment.contains id then throw 4
      let s ← get
      let i := s.mvarNums.getD id s.mvars.size
      if i == s.mvars.size then
        if i == maxMVars then throw 6
        set { s with mvars := s.mvars.push id, mvarNums := s.mvarNums.insert id i }
      pure (.mvar ⟨.num `_paperlean_mv i⟩)
    | .sort u => pure (e.updateSort! (← canonRawLevel mctx u))
    | .const _ us => pure (e.updateConst! (← us.mapM (canonRawLevel mctx)))
    | .app f a => pure (e.updateApp! (← go f) (← go a))
    | .lam _ t b _ => pure (e.updateLambdaE! (← go t) (← go b))
    | .forallE _ t b _ => pure (e.updateForallE! (← go t) (← go b))
    | .letE _ t v b _ => pure (e.updateLetE! (← go t) (← go v) (← go b))
    | .mdata _ b => pure (e.updateMData! (← go b))
    | .proj _ _ b => pure (e.updateProj! (← go b))
    | _ => pure e
  modify fun s => { s with cache := s.cache.insert k r }
  return r
where
  go := canonRaw mctx num maxMVars

/-- The most declarations, and declarations and metavariables, that the context of a problem with a
key reaches. A key costs about as much as the context it holds, and the search for a problem with a
larger one, as in the binders whose types are chains of `letI`, costs less than its key: it runs as
Lean's. -/
private def maxDecls := 24
private def maxContext := 64

/-- The free variables that `key?` finds, in the order found: `collectFVars`, but for the terms
visited, which are told apart by their addresses (comparing two equal terms costs about as much as
visiting one again, which finds no other free variable), and the free variables visited, by their
identifiers, which finds the same variables in the same order. -/
private structure Found where
  fvarSet : FVarIdSet := {}
  fvarIds : Array FVarId := #[]
  visited : Std.HashSet USize := {}
  visitedFVars : Std.HashSet FVarId := {}

private local instance : Inhabited Found := ⟨{}⟩

private def Found.add (s : Found) (id : FVarId) : Found :=
  { s with fvarSet := s.fvarSet.insert id, fvarIds := s.fvarIds.push id }

mutual
/-- `CollectFVars.visit`. -/
private unsafe def Found.visit (e : Expr) (s : Found) : Found :=
  if !e.hasFVar then s else
  match e with
  | .fvar id =>
    if s.visitedFVars.contains id then s else { s.add id with visitedFVars := s.visitedFVars.insert id }
  | _ =>
    let p := ptrAddrUnsafe e
    if s.visited.contains p then s else Found.main e { s with visited := s.visited.insert p }

/-- `CollectFVars.main`, of `collectFVars`. -/
private unsafe def Found.main : Expr → Found → Found
  | .proj _ _ e, s => Found.visit e s
  | .forallE _ d b _, s | .lam _ d b _, s => Found.visit b (Found.visit d s)
  | .letE _ t v b _, s => Found.visit b (Found.visit v (Found.visit t s))
  | .app f a, s => Found.visit a (Found.visit f s)
  | .mdata _ b, s => Found.visit b s
  | .fvar id, s => s.add id
  | _, s => s
end

/-- The problem `type` with local instances `localInsts` as a `Key`, and the free variables in the
order of their numbers, unless the problem has metavariables, the context it reaches has unassigned
ones (or ones that `canonRaw` does not number), or that context is large (`maxDecls`,
`maxContext`): the exclusion then. `type` may have `wildcardFVarId` (in output parameters). -/
private def key? (localInsts : LocalInstances) (type : Expr) (maxResultSize : Nat) :
    MetaM (Except Speculation.Exclusion (Key × Array FVarId)) := do
  if type.hasMVar then
    return .error 4
  let lctx ← getLCtx
  if lctx.contains wildcardFVarId then
    return .error 4
  -- (the free variables reached, in the order found: one state, so that subterms shared between
  -- declarations are visited once; the terms visited stay alive, in `reached`)
  let mut cs : Found := unsafe Found.main type {}
  for li in localInsts do
    if !cs.fvarSet.contains li.fvar.fvarId! then
      cs := cs.add li.fvar.fvarId!
  -- (each declaration with its type and value instantiated, in one metavariable context, so that
  -- what the declarations share is instantiated once)
  let mctx ← getMCtx
  let mut imctx := mctx
  let mut reached : Array (LocalDecl × Expr × Option Expr) := #[]
  let mut next := 0
  while h : next < cs.fvarIds.size do
    -- (the free variables found are all reached: the context is large as soon as they are too many,
    -- before the declarations not yet visited are instantiated)
    if cs.fvarIds.size - (if cs.fvarSet.contains wildcardFVarId then 1 else 0) > maxDecls then
      return .error 6
    let id := cs.fvarIds[next]
    next := next + 1
    if id == wildcardFVarId then continue
    let some d := lctx.find? id | return .error 4
    let (some t, m) := instantiated? imctx d.type | return .error 4
    imctx := m
    cs := unsafe Found.main t cs
    let mut v? := none
    if let some v := d.value? then
      let (some v, m) := instantiated? imctx v | return .error 4
      imctx := m
      cs := unsafe Found.main v cs
      v? := some v
    reached := reached.push (d, t, v?)
  let decls := reached.qsort (·.1.index < ·.1.index)
  let fvars := decls.map (·.1.fvarId)
  let mut num : Std.HashMap FVarId Nat := {}
  for h : i in [0:fvars.size] do
    num := num.insert fvars[i] i
  let canon (e : Expr) : Expr := e.replace fun e =>
    if !e.hasFVar then some e else
    match e with
    | .fvar id => if id == wildcardFVarId then none else some (canonFVar (num.getD id 0))
    | _ => none
  let type : ExactExpr := ⟨canon type⟩
  -- (the types and values as they are, with their metavariables numbered)
  let maxMVars := maxContext - decls.size
  let raw? : Except Speculation.Exclusion
      (Array (ExactExpr × Option ExactExpr × LocalDeclKind) × RawCanon) :=
    (decls.mapM fun ((d, _, _) : LocalDecl × Expr × Option Expr) => do
      let t ← unsafe canonRaw mctx num maxMVars d.type
      let v? ← d.value?.mapM (unsafe canonRaw mctx num maxMVars ·)
      return ((⟨t⟩ : ExactExpr), v?.map ExactExpr.mk, d.kind)).run {}
  let (decls, rc) ← match raw? with
    | .ok r => pure r
    | .error kind => return .error kind
  -- (a value or type with other free variables than those of the problem is not one of the key)
  let ofProblem (e : Expr) : Bool := !e.hasMVar &&
    (!e.hasFVar ||
      (collectFVars {} e).fvarIds.all fun id => id == wildcardFVarId || num.contains id)
  -- (the values and types of the metavariables in one term, so that what they share is instantiated,
  -- checked and renumbered once)
  let some vs := rc.mvars.mapM mctx.getExprAssignmentCore? | return .error 4
  let some ts := rc.mvars.mapM fun id => return (← mctx.findDecl? id).type | return .error 4
  if vs.any (·.hasMVar) then
    return .error 4
  let ts := (instantiateMVarsCore imctx (mkAppN (.bvar 0) ts)).1.getAppArgs
  let all := mkAppN (.bvar 0) (vs ++ ts)
  unless ofProblem all do
    return .error 4
  let all := (canon all).getAppArgs
  let mvars : Array (ExactExpr × ExactExpr) :=
    (all.extract 0 vs.size).zip (all.extract vs.size all.size) |>.map fun (v, t) => (⟨v⟩, ⟨t⟩)
  let some lmvars := rc.lmvars.mapM (mctx.lAssignment.find? ·) | return .error 4
  let synthPendingDepth := (← read).synthPendingDepth
  let configKey := (← getConfigWithKey).key
  let h := decls.foldl (init := mixHash (hash type) (mixHash (hash configKey)
      (mixHash (hash synthPendingDepth) (hash maxResultSize))))
    fun h (t, v?, _) => mixHash h (mixHash (hash t) (hash v?))
  let hash := mvars.foldl (init := h) fun h (v, t) => mixHash h (mixHash (hash v) (hash t))
  let key : Key := {
    hash, type, decls, mvars, lmvars
    localInsts := localInsts.map fun li => (li.className, num.getD li.fvar.fvarId! 0)
    synthPendingDepth, maxResultSize, configKey
    univApprox := (← read).univApprox
    cacheInferType := (← read).cacheInferType
    opts := ← getOptions
    isExporting := (← getEnv).isExporting }
  return .ok (key, fvars)

/-- Replace free-variable leaves, stopping at subexpressions without free variables. -/
@[extern "lean_paperlean_tc_replace_fvars"]
private def replaceFVarLeaves (e : @& Expr) (f : @& (Expr → Option Expr)) : Expr :=
  if !e.hasFVar then e else e.replace fun t =>
    if !t.hasFVar then some t else if t.isFVar then f t else none

/-- The free variables `fvars` replaced by their numbers in `e` (which has no other ones). -/
private def canonExpr (num : Std.HashMap FVarId Nat) (e : Expr) : Expr :=
  if !e.hasFVar then e else replaceFVarLeaves e fun e =>
    match e with
    | .fvar id => num[id]?.map canonFVar
    | _ => none

/-- `e` (from an `Entry`) with the free variables `fvars` put back. -/
private def restoreExpr (fvars : Array FVarId) (e : Expr) : Expr :=
  if !e.hasFVar then e else replaceFVarLeaves e fun e =>
    match e with
    | .fvar ⟨.num p i⟩ => if p == `_paperlean_tc then fvars[i]?.map mkFVar else none
    | _ => none

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
  return some { r with expr := canonExpr num r.expr }

/-- `r` (from an `Entry`) with the free variables `fvars` put back. -/
private def restore (fvars : Array FVarId) (r : Option AbstractMVarsResult) :
    Option AbstractMVarsResult :=
  r.map fun r => { r with expr := restoreExpr fvars r.expr }

/-! The operations of a search on Lean's caches, as kept and as repeated. -/

/-- Whether `n` is a name that a search made with the name generator that was `ngen0` before it and
had index `idx1` after it (also a name of a generator made from one of these, `mkChild`). -/
private def madeBy (ngen0 : NameGenerator) (idx1 : Nat) : Name → Bool
  | .num p i => (i ≥ ngen0.idx && i < idx1 && p == ngen0.namePrefix) || madeBy ngen0 idx1 p
  | .str p _ => madeBy ngen0 idx1 p
  | .anonymous => false

private unsafe def levelMentionsImpl (p : Name → Bool) (u : Level) : Bool := Id.run do
  let mut todo := #[u]
  let mut seen : Std.HashSet USize := {}
  while let some l := todo.back? do
    todo := todo.pop
    if !l.hasMVar then continue
    let key := ptrAddrUnsafe l
    if seen.contains key then continue
    seen := seen.insert key
    match l with
    | .mvar id => if p id.name then return true
    | .succ v => todo := todo.push v
    | .max a b | .imax a b => todo := todo.push b |>.push a
    | _ => pure ()
  return false

@[implemented_by levelMentionsImpl]
private partial def levelMentions (p : Name → Bool) : Level → Bool
  | .mvar id => p id.name
  | .succ u => levelMentions p u
  | .max u v | .imax u v => levelMentions p u || levelMentions p v
  | _ => false

/-- Whether `e` has a free variable whose identifier satisfies `pf`, or a metavariable or universe
metavariable whose name satisfies `pm`. -/
private def mentions (pf : FVarId → Bool) (pm : Name → Bool) (e : Expr) : Bool :=
  (e.hasFVar || e.hasMVar) && (e.findExt? fun e =>
    if !e.hasFVar && !e.hasMVar then .done else
    match e with
    | .fvar id => if pf id then .found else .done
    | .mvar id => if pm id.name then .found else .done
    | .sort u => if u.hasMVar && levelMentions pm u then .found else .done
    | .const _ us => if us.any fun u => u.hasMVar && levelMentions pm u then .found else .done
    | _ => .visit).isSome

/-- The binder names with macro scopes in `es`, and whether `es` hold syntax in metadata (e.g. the
pattern of `Expr.patternWithRef?`, which a type may hold), which compares without its position. -/
private unsafe def hygNames (es : Array Expr) : NameSet × Bool := Id.run do
  let mut seen : Std.HashMap USize Unit := {}
  let mut names : NameSet := {}
  let mut hasSyntax := false
  let mut todo := es.toList
  while true do
    let e :: rest := todo | break
    todo := rest
    if seen.contains (ptrAddrUnsafe e) then continue
    seen := seen.insert (ptrAddrUnsafe e) ()
    match e with
    | .forallE n t b _ | .lam n t b _ =>
      if n.hasMacroScopes then names := names.insert n
      todo := t :: b :: todo
    | .letE n t v b _ =>
      if n.hasMacroScopes then names := names.insert n
      todo := t :: v :: b :: todo
    | .app f a => todo := f :: a :: todo
    | .mdata d b =>
      hasSyntax := hasSyntax || d.entries.any (·.2 matches .ofSyntax _)
      todo := b :: todo
    | .proj _ _ b => todo := b :: todo
    | _ => pure ()
  return (names, hasSyntax)

/-- Whether `e` has a binder name of `names`. -/
private def mentionsBinder (names : NameSet) (e : Expr) : Bool :=
  !names.isEmpty && (e.find? fun
    | .forallE n .. | .lam n .. | .letE n .. => names.contains n
    | _ => false).isSome

/-- Whether the keys `a` and `b` of cache `c`, which the cache takes as the same, are equal, binder
names and annotations included. -/
private unsafe def sameKey (c : UInt8) (a b : NonScalar) : Bool :=
  ptrEq a b ||
    let xs := keyExprs c a
    let ys := keyExprs c b
    xs.size == ys.size && (xs.zip ys).all fun (x, y) => x.equal y

/-! Keys of Lean's caches whose value Lean computes from the key alone, so that a search's lookup of
one finds the value that a miss computes, and a miss changes the state only by the insertions of
entries of such keys (and, for `funInfo`, by the snapshot of what the computation reported, if it
did): the search's path does not depend on whether such an entry is in the cache. -/

/-- Whether `k`, a key of cache `c`, is a `funInfo` of an imported constant without universe
metavariables. Lean's `checkFunInfoCache` computes it with `realizeValue`, which for an imported
constant computes it once for the module (in the environment after the imports, in a state of its
own, taking no names of the caller's) and gives every later call that value. -/
private unsafe def realizedKey (env : Environment) (c : UInt8) (k : NonScalar) : Bool :=
  c == 1 &&
    match (unsafeCast k : InfoCacheKey).expr with
    | .const n us => !us.any (·.hasMVar) && env.isImportedConst n
    | _ => false

/-- The imported constant `n` if it is visible also where private constants are not
(`Environment.isExporting`), so in every environment of the module. -/
private def publicImported? (env : Environment) (n : Name) : Option ConstantInfo :=
  if env.isImportedConst n then envWithoutRecording fun _ => (env.setExporting true).find? n
  else none

/-- Whether `k`, a key of cache `c`, is an `inferType` of an imported constant, visible in every
environment of the module, whose universe levels have no metavariables. Lean's `inferConstType`
computes it as the constant's type with the levels put in, taking no names and changing only
`CoreM`'s cache of these. -/
private unsafe def constTypeKey (env : Environment) (c : UInt8) (k : NonScalar) : Bool :=
  c == 0 &&
    match (unsafeCast k : ExprConfigCacheKey).expr with
    | .const n us => !us.isEmpty && !us.any (·.hasMVar) && (publicImported? env n).isSome
    | _ => false

/-- The number of leading `∀` of `e` as it is (no `mdata` between them). -/
private def numForalls : Expr → Nat
  | .forallE _ _ b _ => numForalls b + 1
  | _ => 0

/-- Whether `k`, a key of cache `c`, is an `inferType` of an application of an imported constant,
visible in every environment of the module, whose universe levels have no metavariables, with at
most as many arguments as the constant's type has leading `∀`. Lean's `inferAppType` computes it
from the type of the constant (a `constTypeKey`, or without the cache if the constant has no
universe levels) by putting the arguments in, without `whnf`. -/
private unsafe def appTypeKey (env : Environment) (c : UInt8) (k : NonScalar) : Bool :=
  c == 0 &&
    let e := (unsafeCast k : ExprConfigCacheKey).expr
    e.isApp &&
      match e.getAppFn with
      | .const n us =>
        !us.any (·.hasMVar) &&
          (publicImported? env n).any fun ci => e.getAppNumArgs ≤ numForalls ci.type
      | _ => false

/-- Whether `k`, a key of cache `c`, is one whose value Lean computes from the key alone. -/
private unsafe def pureKey (env : Environment) (c : UInt8) (k : NonScalar) : Bool :=
  realizedKey env c k || constTypeKey env c k || appTypeKey env c k

/-- The exact equivalence used by `sameKey`, with the cache discriminator. Other cache-key
fields deliberately do not participate: `sameKey` compares only these expressions, with `Expr.equal`
(including binder names and annotations), even when the ordinary cache key compares more fields. -/
private structure OpIndexKey where
  cache : UInt8
  exprs : Array Expr

private local instance : BEq OpIndexKey where
  beq a b := a.cache == b.cache && a.exprs.size == b.exprs.size &&
    (a.exprs.zip b.exprs).all fun (x, y) => x.equal y

private local instance : Hashable OpIndexKey where
  hash k := k.exprs.foldl (fun h e => mixHash h (hash e)) (hash k.cache)

/-- `ops` with the insertion ending each pure miss. Scan backwards, remembering the next insertion
per exact key. A same-key lookup removes its candidate. An ordinary lookup clears every candidate;
an impure insertion clears them too, but is itself a candidate (the forward scan tests equality
before purity). Each operation is classified once. Hash collisions still use exact expression
comparison, so the expected linear table work does not assume collision-free hashes. -/
private unsafe def withInsertAt (env : Environment) (ops : Array CacheOp) : Array CacheOp :=
    Id.run do
  unless ops.any (· matches .pureLookup _ _ none _) do return ops
  let mut out := ops
  let mut next : Std.HashMap OpIndexKey Nat := {}
  let mut i := ops.size
  while i > 0 do
    i := i - 1
    let some op := ops[i]? | break
    match op with
    | .insert c k _ =>
      let key : OpIndexKey := ⟨c, keyExprs c k⟩
      unless pureKey env c k do next := {}
      next := next.insert key i
    | .pureLookup c k found? _ =>
      let key : OpIndexKey := ⟨c, keyExprs c k⟩
      if found?.isNone then
        if let some j := next[key]? then
          out := out.set! i (.pureLookup c k none (some j))
      next := next.erase key
    | .lookup .. => next := {}
  return out

/-- Whether an expression mentions a name that the search made (`made`), and whether it mentions a
variable that is neither of the problem (`num`) nor made by the search. -/
private def isMadeOrOther (num : Std.HashMap FVarId Nat) (made : Name → Bool) :
    (Expr → Bool) × (Expr → Bool) :=
  (mentions (made ·.name) made,
   mentions (fun id => !num.contains id && !made id.name && id != wildcardFVarId) (!made ·))

/-- Whether an expression mentions a name that the search made or a variable that is not of the
problem (`num`): one of `isMadeOrOther`, in one pass. -/
private def isMadeOrOtherEither (num : Std.HashMap FVarId Nat) (made : Name → Bool) : Expr → Bool :=
  mentions (fun id => made id.name || (!num.contains id && id != wildcardFVarId)) fun _ => true

/--
The operations `ops` (`EnvAccess.cache`, in order) of a search, as kept with its entry: the lookups
that found an entry that was there before the search, or that found none, and the insertions, with
the free variables `num` of the problem replaced by their numbers; the lookups of pure keys in the
environment `env` as `pureLookup`. The operations on entries whose keys mention a name that the
search made (`made`) are left out: no later lookup can find these. Fails if an operation mentions a
variable that is neither of the problem nor made by the search. The phase worker keeps `rename`
as an unknown function parameter, so specializing the loop cannot reconstruct its capturing
partial application on every operation.
-/
@[noinline, nospecialize]
private unsafe def keptOpsUsing (rename : Expr → Expr) (env : Environment) (ops : Array EnvAccess)
    (num : Std.HashMap FVarId Nat) (made : Name → Bool) : Except String (Array CacheOp) := do
  let (isMade, _) := isMadeOrOther num made
  let either := isMadeOrOtherEither num made
  -- (the entries that the search inserted)
  let mut inserted : Meta.Cache := {}
  let mut kept := #[]
  let mut memo : ExprRemapMemo := mkPtrMap 8
  for op in ops do
    let .cache c o k v := op | continue
    if c > 3 then throw "an operation on another cache"
    -- (a key that mentions either, but no name that the search made, mentions another variable)
    let mentioned := keyAny c k either
    let dead := mentioned && keyAny c k isMade
    if mentioned && !dead then
      throw "an operation on a cache with other variables"
    if o == 0 then
      -- (a lookup: `v` is what it found; an entry that the search inserted is found again on reuse,
      -- where it is inserted again)
      let mut found? : Option NonScalar := unsafeCast v
      if dead || (found?.isSome && (findIn c inserted k).isSome) then continue
      if let some w := found? then
        if valueAny c w either then
          throw "a cache entry with other variables"
        let (w, next) := (mapValueMemo c rename w).run memo
        memo := next
        found? := some w
      let (k, next) := (mapKeyMemo c rename k).run memo
      memo := next
      kept := kept.push <|
        if pureKey env c k then .pureLookup c k found? none else .lookup c k found?
    else
      inserted := insertIn c inserted k v
      if dead then continue
      if valueAny c v either then
        throw "a cache entry with other variables"
      let (k, next) := (mapKeyMemo c rename k).run memo
      memo := next
      let (v, next) := (mapValueMemo c rename v).run memo
      memo := next
      kept := kept.push (.insert c k v)
  return withInsertAt env kept

private unsafe def keptOps (env : Environment) (ops : Array EnvAccess)
    (num : Std.HashMap FVarId Nat) (made : Name → Bool) : Except String (Array CacheOp) :=
  keptOpsUsing (canonExpr num) env ops num made

/-- A key of the caches of `isDefEq` that no lookup finds: `mark` puts it there, and an `isDefEq`
removes it with all else. -/
private def markKey : DefEqCacheKey :=
  { lhs := .fvar ⟨`_paperlean_mark⟩, rhs := .fvar ⟨`_paperlean_mark⟩, configKey := 0 }

/-- `cache` with its caches of `isDefEq` made other objects, which a search leaves as they are unless
it empties them. -/
private def mark (cache : Meta.Cache) : Meta.Cache :=
  { cache with
    defEqTrans := cache.defEqTrans.insert markKey true
    defEqPerm := cache.defEqPerm.insert markKey true }

/-- Takes the marks of `marked`, made from `cache`, out of the state, in which a search ended: whether
it emptied the transient and the permanent cache of `isDefEq`. (Entries are added only after they are
emptied.) -/
private unsafe def unmark (cache marked : Meta.Cache) : MetaM (Bool × Bool) := do
  let now := (← get).cache
  let trans := !ptrEq now.defEqTrans marked.defEqTrans
  let perm := !ptrEq now.defEqPerm marked.defEqPerm
  modify fun s => { s with
    cache.defEqTrans := if trans then s.cache.defEqTrans else cache.defEqTrans
    cache.defEqPerm := if perm then s.cache.defEqPerm else cache.defEqPerm }
  return (trans, perm)

/-- What a reuse of the search `p`, of which `num` numbers the free variables and `made` tells the names
that it made, repeats on the caches of `isDefEq`, if it found nothing. Its entries of the transient cache
are not kept: a lookup there has a key with a metavariable that is not of the search, and they have
none. -/
private def DefEqEffect.of (p : Pending) (num : Std.HashMap FVarId Nat) (made : Name → Bool) :
    Except String DefEqEffect := do
  if p.result.isSome then
    return {}
  let (isMade, isOther) := isMadeOrOther num made
  let mut perm := #[]
  for (k, v) in p.perm.toList do
    if isMade k.lhs || isMade k.rhs then continue
    if isOther k.lhs || isOther k.rhs then
      throw "an entry of a cache of `isDefEq` with other variables"
    perm := perm.push ({ k with lhs := canonExpr num k.lhs, rhs := canonExpr num k.rhs }, v)
  return { emptiesTrans := p.emptiedTrans, emptiesPerm := p.emptiedPerm, perm }

/-- `cache` as a search that had the effect `d` leaves it, for the free variables `fvars` of the
problem. (A key holds its expressions in the order of `Expr.quickLt`, as `mkDefEqCacheKey` makes it.) -/
private def DefEqEffect.apply (d : DefEqEffect) (fvars : Array FVarId) (cache : Meta.Cache) :
    Meta.Cache :=
  let perm := if !d.emptiesPerm then cache.defEqPerm else
    d.perm.foldl (init := {}) fun c (k, v) =>
      let (a, b) := (restoreExpr fvars k.lhs, restoreExpr fvars k.rhs)
      c.insert (if Expr.quickLt a b then { k with lhs := a, rhs := b }
        else { k with lhs := b, rhs := a }) v
  { cache with defEqTrans := if d.emptiesTrans then {} else cache.defEqTrans, defEqPerm := perm }

/-- Whether the operations `ops` (`EnvAccess.cache`, in order) of a search make the caches `cache1`
from `cache0`: an operation that the hooks of Lean's caches do not see, or a cache emptied or restored,
would show here (`PAPERLEAN_REUSE_ORACLE`). -/
private unsafe def opsMakeCaches (ops : Array EnvAccess) (cache0 cache1 : Meta.Cache) : Bool := Id.run do
  let mut cache := cache0
  let mut inserted : Array (UInt8 × NonScalar) := #[]
  for op in ops do
    let .cache c o k v := op | continue
    if o == 0 then
      unless sameObj? (unsafeCast v) (findIn c cache k) do return false
    else
      cache := insertIn c cache k v
      inserted := inserted.push (c, k)
  return inserted.all (fun (c, k) => sameObj? (findIn c cache k) (findIn c cache1 k)) &&
    madeByInsertions cache0 cache cache1

/--
The caches after repeating the operations `ops` (of an entry) on `cache` with the free variables
`fvars` of the problem, the operations as made, and the `funInfo` entries that Lean's search computes
again (`fill`) with the values that the recorded search found; `none` if a lookup does not find what
the search found. `keepMade` keeps the insertions needed by a recording, oracle or possible `funInfo`
fill; `keepLookups` keeps lookups, needed only by an enclosing recording. Neither flag controls
checking or replaying an op.

The lookups of pure keys may find otherwise: Lean's search finds the same values either way, and
then makes the same operations on other keys. One that found an entry and finds none now is a miss
of Lean's search, which computes the value again and inserts the entries of the computation (of
pure keys): `fill` does it for `funInfo`, whose computation may report something; the entries of
`inferType` are left out. One that found none and finds an entry now, with the value that the
search inserted under the key, is a hit of Lean's search, which then neither makes the operations
up to that insertion (on pure keys only, `insertAt?`) nor the insertion.
`rename` is the phase's free-variable restoration, kept as a runtime closure across this compilation
boundary and shared by all operations.
-/
@[noinline, nospecialize]
private unsafe def replayOpsUsing (rename : Expr → Expr) (ops : Array CacheOp) (cache : Meta.Cache)
    (keepMade keepLookups : Bool) :
    Option (Meta.Cache × Array (UInt8 × UInt8 × NonScalar × NonScalar) ×
      Array (NonScalar × NonScalar)) := Id.run do
  let mut cache := cache
  let mut made : Array (UInt8 × UInt8 × NonScalar × NonScalar) := #[]
  let mut fills := #[]
  let mut memo : ExprRemapMemo := mkPtrMap 8
  let mut i := 0
  while h : i < ops.size do
    match ops[i] with
    | .lookup c k found? =>
      let (k, next) := (mapKeyMemo c rename k).run memo
      memo := next
      let now? := findIn c cache k
      match now?, found? with
      | some v, some w =>
        let (w, next) := (mapValueMemo c rename w).run memo
        memo := next
        unless sameValue c v w do return none
      | none, none => pure ()
      | _, _ => return none
      if keepLookups then made := made.push (c, 0, k, unsafeCast now?)
    | .insert c k v =>
      let (k, next) := (mapKeyMemo c rename k).run memo
      memo := next
      let (v, next) := (mapValueMemo c rename v).run memo
      memo := next
      cache := insertIn c cache k v
      if keepMade then made := made.push (c, 1, k, v)
    | .pureLookup c k found? insertAt? =>
      let (k, next) := (mapKeyMemo c rename k).run memo
      memo := next
      let now? := findIn c cache k
      match now?, found? with
      | some v, some w =>
        let (w, next) := (mapValueMemo c rename w).run memo
        memo := next
        unless sameValue c v w do return none
      | none, none => pure ()
      | none, some w =>
        if c == 1 then
          let w := mapValue c rename w
          fills := fills.push (k, w)
          cache := insertIn c cache k w
        i := i + 1
        continue
      | some v, none =>
        let some j := insertAt? | return none
        let some (.insert _ _ w) := ops[j]? | return none
        let (w, next) := (mapValueMemo c rename w).run memo
        memo := next
        unless sameValue c v w do return none
        if keepLookups then made := made.push (c, 0, k, unsafeCast now?)
        i := j + 1
        continue
      if keepLookups then made := made.push (c, 0, k, unsafeCast now?)
    i := i + 1
  return some (cache, made, fills)

private unsafe def replayOps (fvars : Array FVarId) (ops : Array CacheOp) (cache : Meta.Cache)
    (keepMade keepLookups : Bool) :
    Option (Meta.Cache × Array (UInt8 × UInt8 × NonScalar × NonScalar) ×
      Array (NonScalar × NonScalar)) :=
  replayOpsUsing (restoreExpr fvars) ops cache keepMade keepLookups

/-- Lean's `getFunInfo` of the keys `fills` (`realizedKey`, with the configuration key of the
lookup), which Lean's search computes again where the recorded search found an entry: whether each
gives the value found. Inserts the entries (and reports what the computation reported) as Lean's
`checkFunInfoCache` does. -/
private unsafe def fill (fills : Array (NonScalar × NonScalar)) : MetaM Bool := do
  for (k, w) in fills do
    let k : InfoCacheKey := unsafeCast k
    let info? ← try
        some <$> withReader (fun ctx => { ctx with keyedConfig.key := k.configKey }) do
          match k.nargs? with
          | some n => getFunInfoNArgs k.expr n
          | none => getFunInfo k.expr
      catch _ => pure none
    let some info := info? | return false
    unless sameValue 1 (unsafeCast info) w do
      return false
  return true

/-- Whether the result, the keys and values of `ops` or the keys of `perm` mention a binder name of
`names`. (The caches of `inferType` and `whnf` compare keys with their binder names, `Expr.equal`; all
keep the key of the last insertion.) -/
private unsafe def opsMention (names : NameSet) (r : Option AbstractMVarsResult)
    (ops : Array CacheOp) (perm : Array (DefEqCacheKey × Bool)) : Bool :=
  !names.isEmpty &&
    (r.any (fun r => (r.mvars.push r.expr).any (mentionsBinder names)) ||
      perm.any (fun (k, _) => mentionsBinder names k.lhs || mentionsBinder names k.rhs) ||
      ops.any fun
        | .lookup c k found? =>
          (keyExprs c k ++ (found?.map (valueExprs c)).getD #[]).any (mentionsBinder names)
        | .insert c k v => (keyExprs c k ++ valueExprs c v).any (mentionsBinder names)
        | .pureLookup c k found? _ =>
          (keyExprs c k ++ (found?.map (valueExprs c)).getD #[]).any (mentionsBinder names))

/-- How a search changed the state `core0`, `meta0` into `core1`, `meta1` beyond what a reuse
repeats (the name generator, macro scopes, Lean's caches), if it did. -/
private unsafe def stateChange? (core0 : Core.State) (meta0 : Meta.State) (core1 : Core.State)
    (meta1 : Meta.State) : Option String :=
  -- (a change of the environment, a record of a module use, empties Lean's caches)
  if !ptrEq core1.env core0.env then some "a change of the environment"
  else if !(ptrEq core1.messages core0.messages && ptrEq core1.traceState core0.traceState &&
      ptrEq core1.infoState core0.infoState && ptrEq core1.snapshotTasks core0.snapshotTasks &&
      ptrEq core1.auxDeclNGen core0.auxDeclNGen && ptrEq meta1.mctx meta0.mctx &&
      ptrEq meta1.postponed meta0.postponed &&
      ptrEq meta1.zetaDeltaFVarIds meta0.zetaDeltaFVarIds && ptrEq meta1.diag meta0.diag) then
    some "a change of the state"
  else none

/-- What is kept of Lean's search for the problem `key` with free variables `fvars`, which started in
the states `core0` and `meta0`, now ended with result `r` and dependencies `raw?`; or why nothing is.
What it costs little to tell is told now, the rest when a problem first has the key (`finished`). -/
private def pending? (key : Key) (fvars : Array FVarId) (core0 : Core.State) (meta0 : Meta.State)
    (r : Option AbstractMVarsResult) (raw? : Except String EnvDeps.Raw)
    (emptied : Bool × Bool) : MetaM (Except String Pending) := do
  let raw ← match raw? with
    | .ok raw => pure raw
    | .error why => return .error s!"not recordable: {why}"
  let core1 ← getThe Core.State
  let meta1 ← get
  if let some why := unsafe stateChange? core0 meta0 core1 meta1 then
    return .error why
  -- (a name made with macro scopes of this command would differ in another)
  if core1.nextMacroScope != core0.nextMacroScope then
    return .error "macro scopes"
  let ngen0 := core0.ngen
  let ngen1 := core1.ngen
  unless ngen1.namePrefix == ngen0.namePrefix && ngen0.idx ≤ ngen1.idx do
    return .error "another name generator"
  if Speculation.reuseOracle then
    unless unsafe opsMakeCaches raw.deps.cacheOps meta0.cache meta1.cache do
      Speculation.fail "typeclass cache: the recorded operations do not make the caches"
  return .ok {
    key, fvars, result := r, raw, ngen0, ngenEnd := ngen1.idx, emptiedTrans := emptied.1
    emptiedPerm := emptied.2, perm := if r.isNone && emptied.2 then meta1.cache.defEqPerm else {} }

/-- The entry of the search `p`, in the environment `env`, whose imported constants are those of the
search's; or why it is not kept. -/
private unsafe def Pending.finish (env : Environment) (p : Pending) : Except String Entry := do
  let deps := p.raw.deps
  let some result := canonResult? p.fvars p.result | throw "a result with other free variables"
  let (names, hasSyntax) := hygNames p.key.exprs
  -- (an equal key may hold other positions, and the result holds what the problem held)
  if hasSyntax then
    throw "a problem with syntax in its metadata"
  let mut num : Std.HashMap FVarId Nat := {}
  for h : i in [0:p.fvars.size] do
    num := num.insert p.fvars[i] i
  let made := madeBy p.ngen0 p.ngenEnd
  let ops ← keptOps env deps.cacheOps num made
  let mayFill := ops.any fun
    | .pureLookup c _ (some _) _ => c == 1
    | _ => false
  let defEq ← DefEqEffect.of p num made
  return {
    key := p.key, deps := { deps with cacheOps := #[] }, result, names := p.ngenEnd - p.ngen0.idx, ops, mayFill
    defEq, namesFree := !opsMention names result ops defEq.perm }

/-- `stored` (of the key `key`) as entries, those that were pending now finished, and put back; what
is not kept goes, with its reason noted. -/
private def finished (env : Environment) (key : Key) (stored : Array Stored) :
    MetaM (Array Entry) := do
  if stored.isEmpty then
    return #[]
  let mut entries := #[]
  let mut changed := false
  let mut cheap := false
  for s in stored do
    match s with
    | .entry e => entries := entries.push e
    | .pending p =>
      changed := true
      match envWithoutRecording fun _ => unsafe p.finish env with
      | .ok e => entries := entries.push e
      | .error why => noteReason s!"not kept: {why}"
    | .cheap => cheap := true
  if changed then
    modifyEntries (·.insert key ((if cheap then #[.cheap] else #[]) ++ entries.map .entry))
  return entries

/-- The state of the problem's search before a reuse, for `PAPERLEAN_REUSE_ORACLE`. -/
private structure OracleState where
  ngen : NameGenerator
  nextMacroScope : Nat
  coreCache : Core.Cache
  cache : Meta.Cache

/-- Compares the reuse of entry `e` with Lean's search from the current state, in which nothing is
reused, for `PAPERLEAN_REUSE_ORACLE`: its result, the names and macro scopes it takes, and that it
leaves the rest of the state as a kept search must (`stateChange?`); returns the state before, which
the search leaves (but for the comparison) as it was, and Lean's caches after the search, for
`compareEffects`. -/
private def oracle (fvars : Array FVarId) (e : Entry)
    (search : MetaM (Option AbstractMVarsResult)) : MetaM (Option (OracleState × Meta.Cache)) := do
  let core0 ← getThe Core.State
  let meta0 ← get
  let before : OracleState := {
    ngen := core0.ngen, nextMacroScope := core0.nextMacroScope, coreCache := core0.cache
    cache := meta0.cache }
  let paused ← envPause
  let fresh? ← Speculation.withoutReuse <| withoutModifyingState do
    try
      let r ← search
      let core1 ← getThe Core.State
      return some (r, core1.ngen.idx - before.ngen.idx,
        core1.nextMacroScope - before.nextMacroScope, (← get).cache,
        unsafe stateChange? core0 meta0 core1 (← get))
    catch _ => return none
  envResume paused
  -- (what `withoutModifyingState` does not restore)
  modifyThe Core.State fun s => { s with
    ngen := before.ngen, nextMacroScope := before.nextMacroScope, cache := before.coreCache }
  modify fun s => { s with cache := before.cache }
  let some (fresh, names, scopes, cache1, change?) := fresh? |
    Speculation.fail "typeclass cache: Lean's search fails"
    return none
  let sameResult := match canonResult? fvars fresh, e.result with
    | some (some f), some r =>
      f.expr.equal r.expr && f.paramNames == r.paramNames && f.numMVars == r.numMVars
    | some none, none => true
    | _, _ => false
  if !sameResult then
    Speculation.fail "typeclass cache: Lean's search gives another result"
  if let some why := change? then
    Speculation.fail s!"typeclass cache: Lean's search makes {why}"
  let reuseNames := if Speculation.fault == "tc-names" then e.names + 1 else e.names
  if names != reuseNames || scopes != 0 then
    Speculation.fail s!"typeclass cache: Lean's search takes {names} names and {scopes} macro \
      scopes, the reuse {reuseNames} and none"
  return some (before, cache1)

private unsafe def findEntryIn (c : UInt8) (cache : Meta.Cache) (k : NonScalar) :
    Option (NonScalar × NonScalar) :=
  if c == 0 then unsafeCast (cache.inferType.findEntry? (unsafeCast k))
  else if c == 1 then unsafeCast (cache.funInfo.findEntry? (unsafeCast k))
  else if c == 2 then unsafeCast (cache.synthInstance.findEntry? (unsafeCast k))
  else unsafeCast (cache.whnf.findEntry? (unsafeCast k))

/-- Compares the caches after a reuse (`cache`) with those after Lean's search (`cache1`, from the
oracle) on the entries that the reuse inserted (`made`), keys and values, for
`PAPERLEAN_REUSE_ORACLE`. -/
private unsafe def compareEffects (cache cache1 : Meta.Cache)
    (made : Array (UInt8 × UInt8 × NonScalar × NonScalar)) : MetaM Unit := do
  for (c, o, k, _) in made do
    if o == 1 then
      match findEntryIn c cache k, findEntryIn c cache1 k with
      | some (k', v), some (k1, w) =>
        unless sameKey c k' k1 do
          Speculation.fail "typeclass cache: Lean's search caches an entry under another key"
        unless sameValue c v w do
          Speculation.fail "typeclass cache: Lean's search caches another value"
      | _, _ => Speculation.fail "typeclass cache: Lean's search does not cache an entry"

/-- Whether `a` and `b`, keys that the caches of `isDefEq` take as the same, are equal, binder names and
annotations included. -/
private def sameDefEqKey (a b : DefEqCacheKey) : Bool :=
  a.lhs.equal b.lhs && a.rhs.equal b.rhs

/-- Compares the caches of `isDefEq` after the reuse of a search that found nothing (`cache`) with those
after Lean's search (`cache1`, which took `names` names from `ngen0`), but for entries of the search
that no lookup finds (`DefEqEffect.of`), for `PAPERLEAN_REUSE_ORACLE`. -/
private def compareDefEq (cache cache1 : Meta.Cache) (ngen0 : NameGenerator) (names : Nat) :
    MetaM Unit := do
  let made := madeBy ngen0 (ngen0.idx + names)
  let isMade := mentions (made ·.name) made
  let dead (k : DefEqCacheKey) := isMade k.lhs || isMade k.rhs
  for (k, v) in cache1.defEqPerm.toList do
    unless dead k || (cache.defEqPerm.findEntry? k).any fun (k', w) => w == v && sameDefEqKey k k' do
      Speculation.fail "typeclass cache: a reuse does not leave Lean's entry of the permanent cache of `isDefEq`"
  for (k, _) in cache.defEqPerm.toList do
    unless cache1.defEqPerm.contains k do
      Speculation.fail "typeclass cache: a reuse leaves another entry of the permanent cache of `isDefEq`"
  for (k, _) in cache1.defEqTrans.toList do
    unless dead k || !(k.lhs.hasMVar || k.rhs.hasMVar) ||
        (cache.defEqTrans.findEntry? k).any (sameDefEqKey k ·.1) do
      Speculation.fail "typeclass cache: a reuse does not leave Lean's entry of the transient cache of `isDefEq`"
  for (k, _) in cache.defEqTrans.toList do
    unless cache1.defEqTrans.contains k do
      Speculation.fail "typeclass cache: a reuse leaves another entry of the transient cache of `isDefEq`"

/-- `search` for a problem with metavariables in other than output parameters, which no entry has. -/
def withoutCache (search : MetaM (Option AbstractMVarsResult)) :
    MetaM (Option AbstractMVarsResult) := do
  if Speculation.reuse then
    let heartbeats ← IO.getNumHeartbeats
    noteExcluded 4
    setHeartbeats heartbeats
  search

/--
`search` (Lean's search for the problem `type` with local instances `localInsts`, of
`synthInstanceCore?`), or the result of the same search in an earlier command whose dependencies on
the environment and whose lookups in Lean's caches hold, with the search's effects on the state
repeated. For a problem with metavariables in output parameters, `type` is its `cacheKeyType`, on
which alone the search depends: it replaces the output parameters with fresh metavariables
(`preprocessOutParam`).
-/
def withCache (localInsts : LocalInstances) (type : Expr) (maxResultSize : Nat)
    (search : MetaM (Option AbstractMVarsResult)) : MetaM (Option AbstractMVarsResult) := do
  let env ← getEnv
  -- (`nativeAvailable` first: the stage0 `lean` that builds stage1 has none of this module's state)
  unless nativeAvailable env && Speculation.reuse do
    return (← search)
  -- (the cache's own work counts no heartbeats)
  let heartbeats ← IO.getNumHeartbeats
  let ctx ← read
  let onThread ← Speculation.onElabThread
  let opts ← getOptions
  let ngen ← getNGen
  let excluded? : Option Speculation.Exclusion :=
    if !onThread || env.asyncPrefix?.isSome then some 0
    else if !usableUnder opts then some 1
    else if ctx.customCanUnfoldPredicate?.isSome then some 2
    else if ctx.trackZetaDelta || !ctx.zetaDeltaSet.isEmpty then some 3
    else if ngen.namePrefix == grindNamePrefix then some 5
    else none
  if let some kind := excluded? then
    noteExcluded kind
    setHeartbeats heartbeats
    return (← search)
  let (key, fvars) ← match ← key? localInsts type maxResultSize with
    | .ok k => pure k
    | .error kind =>
      noteExcluded kind
      setHeartbeats heartbeats
      return (← search)
  -- (an update of the key's entries inserts the key found, which compares with it at once)
  let some (key0, stored) ← getStored? key |
    noteExcluded 0
    setHeartbeats heartbeats
    return (← search)
  let entries ← finished env key0 stored
  let ns ← getCurrNamespace
  let openDecls ← getOpenDecls
  let mut failed := false
  for e in entries do
    unless e.deps.hold env ns openDecls do
      -- (one reason for each problem, as for the numbers of `stats`)
      unless failed do
        failed := true
        if let some a := e.deps.firstFailure? env ns openDecls then
          noteReason s!"not reused: {EnvDeps.reason env a}"
      continue
    unless e.namesFree || e.key.sameNames key do
      noteReason "not reused: other binder names with macro scopes"
      continue
    -- (the search's lookups in Lean's caches find what they found: its path is the same)
    -- (a different witness from the fresh `envRecording key` below: do not common its probe)
    -- (oracle runs with reuse off; fills inspect imported constants, neither starts a recording)
    let keepLookups := envRecording e
    let keepMade := e.mayFill || Speculation.reuseOracle || keepLookups
    let some (cache, made, fills) := unsafe replayOps fvars e.ops (← get).cache keepMade keepLookups |
      noteReason "not reused: a lookup in a cache finds something else"
      continue
    -- (Lean's search from the same state, which the oracle leaves as it was)
    let oracle? ← if Speculation.reuseOracle then oracle fvars e search else pure none
    -- (the entries of `funInfo` that Lean's search computes again, before the reuse's insertions)
    let mut cache := cache
    if !fills.isEmpty then
      unless ← unsafe fill fills do
        noteReason "not reused: Lean's funInfo is not the one found"
        continue
      cache := made.foldl (init := (← get).cache) fun c (cc, o, k, v) =>
        if o == 1 then unsafe insertIn cc c k v else c
    statsRef.modify fun (r, n, f) => (r + 1, n, f)
    -- (a recording that this search is part of depends on what the reused search read)
    envRecordAll e.deps.accesses (unsafe unsafeCast e.deps.checks)
    if envRecording key then
      for (c, o, k, v) in made do
        noteCache c o k v
    cache := e.defEq.apply fvars cache
    modify fun s => { s with cache }
    if let some (before, cache1) := oracle? then
      unsafe compareEffects cache cache1
        (made ++ fills.map fun (k, w) => ((1 : UInt8), (1 : UInt8), k, w))
      if e.result.isNone then
        compareDefEq cache cache1 before.ngen e.names
    modifyThe Core.State fun s => { s with ngen.idx := s.ngen.idx + e.names }
    let r := restore fvars e.result
    setHeartbeats heartbeats
    return r
  statsRef.modify fun (r, n, f) => (r, n + 1, if entries.isEmpty then f else f + 1)
  if stored.any (· matches .cheap) then
    noteReason "not recorded: the last search was cheaper than a reuse"
    setHeartbeats heartbeats
    let r ← search
    let after ← IO.getNumHeartbeats
    if after - heartbeats ≥ minHeartbeats then
      modifyEntries fun m => m.insert key0 (entries.map .entry)
    setHeartbeats after
    return r
  let core0 ← getThe Core.State
  let meta0 ← get
  let marked := mark meta0.cache
  modify fun s => { s with cache := marked }
  let emptied ← (IO.mkRef (false, false) : BaseIO _)
  let rec_ ← EnvDeps.start
  setHeartbeats heartbeats
  -- (ending the recording counts no heartbeats, also on an exception)
  let r ← tryFinally search do
    let heartbeats ← IO.getNumHeartbeats
    discard rec_.stop
    emptied.set (← unsafe unmark meta0.cache marked)
    setHeartbeats heartbeats
  let after ← IO.getNumHeartbeats
  if after - heartbeats < minHeartbeats then
    noteReason "not kept: cheaper than a reuse"
    modifyEntries fun m =>
      m.insert key0 ((#[Stored.cheap] ++ entries.map Stored.entry).take maxEntriesPerKey)
  else match ← pending? key fvars core0 meta0 r (← rec_.stop) (← emptied.get) with
  | .ok p =>
    let stored := #[Stored.pending p] ++ entries.map .entry
    modifyEntries fun m => m.insert key0 (stored.take maxEntriesPerKey)
  | .error why => noteReason s!"not kept: {why}"
  setHeartbeats after
  return r

end Lean.PaperLean.TCCache
