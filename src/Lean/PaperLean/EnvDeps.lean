/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lean.Environment
public import Lean.Data.OpenDecl
public import Lean.ResolveName
import all Lean.Environment
import Std.Data.HashMap.Basic

-- (no `SizeOf` instances for PaperLean's types: an instance of a module of `Lean` would be one of
-- every environment that imports it, which Lean's searches would try)
set_option genSizeOf false
set_option genInjectivity false

public section

/-!
The dependencies of a computation on the environment, recorded so that its result can be reused in
another environment where every access gives the same answer (`Lean.PaperLean.TCCache`,
`Lean.PaperLean.SectionVars`).

While a thread records (`Lean.PaperLean.Base`, `src/paperlean/env_recorder.cpp`), each read of the
environment through `Lean.Environment`'s functions is recorded with a check:
* each extension state read (`EnvExtension.getState`) must be the same object, or for the parts of
  a state that some reads record instead (`EnvAccess.extPart`, e.g. the instances of a class in
  `Lean.PaperLean.TCCache.getInstancesUnify`), those parts must be;
* each lookup of a constant that is not imported (`Environment.findAsync?` and the functions built
  on it) must find a constant, or not, as before (imported constants of a visibility do not change);
* each resolution of a global name or namespace (`ResolveName.resolveGlobalName`,
  `ResolveName.resolveNamespace`) must give the same answer with the namespace and the open
  declarations of the reuse, if it was made with the current ones of the recording (the accesses
  made for it are not recorded); a resolution made with others, e.g. with more open declarations
  (`open ... in`), must give the same answer with these, and the reuse must have the recording's.

Reads that cannot be checked make the recording unusable: of the kernel environment, of all of the
module's constants, through `Environment.findTask`; so do tasks that the thread starts, and tactics.
A recording holds only code that records what it reads, which is not a matter of checking code: Lean's
own, which reads the environment through these functions and global references only where they do not
change after the imports; and macros, which cannot read the environment. Macros read the current
namespace through a function that records it (`Lean.Elab.expandMacroImpl?`). Any other code that
is not Lean's own makes the recording unusable: an elaborator (`Whitelist.noteEntry`, for every
attribute's entries but those of `macro`), unless it is on the whitelist (`Lean.PaperLean.Whitelist`),
and code that Lean's own elaborators evaluate (`Environment.evalConst`). Tactics run whatever is
registered for them, and are not recorded at all.
Lean's own code reads the current namespace and open declarations otherwise than to resolve names
where they decide the result only for `with_decl_name% ?`, which records them (`EnvAccess.scope`: a
reuse then requires the same ones), and for `scoped` attributes, which make the recording unusable.
Whether realizations are enabled for a constant decides whether `getFunInfo` takes names from the
caller's generator, so it is recorded too (`EnvAccess.realizations`).
A recording ends usable if the computation changed the environment only by records of module uses
(`Lean.ExtraModUses`), which it leaves to its users, which keep no computation that changed the
environment; the reads of these extensions, which only decide whether to add an entry, are not
recorded (`hasModuleUses` checks that a computation that found the entries that it needed finds them
again).

The operations of the computation on Lean's caches of `MetaM` (`EnvAccess.cache`, `noteCache`) are
recorded in order, with no check: the user of the recording decides which of them must give the
same answer on reuse and repeats the others (`Lean.PaperLean.TCCache`).
-/

namespace Lean.PaperLean.EnvDeps

/-- The recorded dependencies of a computation. -/
structure Deps where
  /-- Checks of an environment, current namespace and open declarations. -/
  checks : Array (Environment → Name → List OpenDecl → Bool)
  /-- The access of each check. -/
  accesses : Array EnvAccess
  /-- The operations on Lean's caches (`EnvAccess.cache`), in order. -/
  cacheOps : Array EnvAccess := #[]

-- (the instances of PaperLean's types are local: an instance of a module of `Lean` would be one of
-- every environment that imports it, which Lean's searches would try)
local instance : Inhabited Deps := ⟨{ checks := #[], accesses := #[] }⟩

/-- Whether the dependencies hold in `env` with namespace `ns` and open declarations `openDecls`.
(The checks read the environment unrecorded: a recording that reuses the computation records the
computation's accesses, `envRecordAll`.) -/
def Deps.hold (d : Deps) (env : Environment) (ns : Name) (openDecls : List OpenDecl) : Bool :=
  envWithoutRecording fun _ => d.checks.all (· env ns openDecls)

/-- The access of the first check that does not hold, if any. -/
def Deps.firstFailure? (d : Deps) (env : Environment) (ns : Name) (openDecls : List OpenDecl) :
    Option EnvAccess := envWithoutRecording fun _ => Id.run do
  for c in d.checks, a in d.accesses do
    unless c env ns openDecls do
      return some a
  return none

/-- A description of an access, for debugging. -/
def describe (env : Environment) : EnvAccess → String
  | .ext idx mode decl =>
    let _ := env
    s!"extension {extName idx} (mode {mode}{if decl.isAnonymous then "" else s!", {decl}"})"
  | .extPart idx part => s!"extension {extName idx} (part {part})"
  | .const n _ => s!"constant {n}"
  | .resolve id .. => s!"name {id}"
  | .resolveNamespace id .. => s!"namespace {id}"
  | .cache c op .. => s!"operation {op} on cache {c}"
  | .scope decl => s!"current namespace and open declarations, for {decl}"
  | .realizations c => s!"realizations of {c}"
where
  extName (idx : Nat) : String :=
    let exts := unsafe unsafeBaseIO persistentEnvExtensionsRef.get
    exts.find? (·.toEnvExtension.idx == idx) |>.map (·.name.toString) |>.getD s!"#{idx}"

/-- What an access that does not hold depends on, for the summary of a build: without the names of
constants and parts, of which there would be as many reasons. -/
def reason (env : Environment) : EnvAccess → String
  | .ext idx .. | .extPart idx _ => s!"a change of the extension {describe.extName idx}"
  | .const .. => "a change of the constants"
  | .resolve .. | .resolveNamespace .. => "a name that resolves otherwise now"
  | .cache .. => "a change of Lean's caches"
  | .scope decl =>
    let _ := env
    s!"another namespace or other open declarations, which {decl} may read"
  | .realizations .. => "a constant whose realizations are enabled otherwise now"

/-- The open declarations of an access. -/
private unsafe def openDeclsOfImpl (o : NonScalar) : List OpenDecl := unsafeCast o

@[implemented_by openDeclsOfImpl]
private opaque openDeclsOf (o : NonScalar) : List OpenDecl

/-- What decides the answer to an access, for keeping one check of accesses with the same. -/
private structure AccessKey where
  kind : Nat
  idx : Nat
  name : Name
  flag : Bool
  extra : Nat := 0
  ns : Name := .anonymous
  openDecls : List OpenDecl := []

private local instance : BEq AccessKey where
  beq a b := a.kind == b.kind && a.idx == b.idx && a.name == b.name && a.flag == b.flag &&
    a.extra == b.extra && a.ns == b.ns && a.openDecls == b.openDecls

private local instance : Hashable AccessKey where
  hash k := mixHash (hash (k.kind, k.idx, k.name, k.flag, k.extra)) (hash k.ns)

private def accessKey : EnvAccess → Option AccessKey
  | .ext idx mode decl => some { kind := 0, idx, name := decl, flag := mode == 0, extra := mode }
  | .const n skipRealize => some { kind := 1, idx := 0, name := n, flag := skipRealize }
  | .resolve id ns openDecls =>
    some { kind := 2, idx := 0, name := id, flag := false, ns, openDecls := openDeclsOf openDecls }
  | .resolveNamespace id ns openDecls =>
    some { kind := 3, idx := 0, name := id, flag := false, ns, openDecls := openDeclsOf openDecls }
  | .extPart idx part => some { kind := 4, idx, name := part, flag := false }
  | .realizations c => some { kind := 5, idx := 0, name := c, flag := false }
  | .scope decl => some { kind := 6, idx := 0, name := decl, flag := false }
  | .cache .. => none

/-- The extensions of module uses (`Lean.ExtraModUses`), whose reads are not recorded. Apart from the
entries of the module, which decide only whether an entry is added again, their states hold only
imported data. Set by `Lean.PaperLean.SectionVars`: this module lies below `Lean.ExtraModUses`, which
`Lean.Meta.SynthInstance` does not import. -/
builtin_initialize moduleUseExtsRef : IO.Ref (Array Nat) ← IO.mkRef #[]

/-- Whether `a` and `b` are equal but in the states of the extensions `allowed`. -/
private unsafe def sameButImpl (a b : Environment) (allowed : Array Nat) : Bool :=
  ptrEq a.asyncConstsMap b.asyncConstsMap && ptrEq a.asyncCtx? b.asyncCtx? &&
    ptrEq a.importRealizationCtx? b.importRealizationCtx? &&
    ptrEq a.localRealizationCtxMap b.localRealizationCtxMap &&
    ptrEq a.allRealizations b.allRealizations &&
    a.isExporting == b.isExporting && ptrEq a.serverBaseExts b.serverBaseExts &&
    sameKernel a.base.private b.base.private && sameKernel a.base.public b.base.public
where
  sameKernel (x y : Kernel.Environment) : Bool :=
    ptrEq x.constants y.constants && x.quotInit == y.quotInit &&
      ptrEq x.diagnostics y.diagnostics && ptrEq x.const2ModIdx y.const2ModIdx &&
      ptrEq x.irBaseExts y.irBaseExts && ptrEq x.header y.header &&
      x.extensions.size == y.extensions.size &&
      (List.range x.extensions.size).all fun i =>
        allowed.contains i || ptrEq x.extensions[i]! y.extensions[i]!

@[implemented_by sameButImpl]
private opaque sameBut (a b : Environment) (allowed : Array Nat) : Bool

/-- The check of a resolution recorded with `check`, made with namespace `ns` and open declarations
`openDecls` in a recording that started with `ns0` and `openDecls0`: with the namespace and open
declarations of the reuse (as `check` takes them) if these are those of the recording, else with
the resolution's, and the reuse must have the recording's. (The resolution of a dotted identifier
(`Elab.App`) takes the root namespace whatever the current one: for a recording in the root
namespace, the check holds in both.) -/
private def resolutionCheck (check : Environment → Name → List OpenDecl → Bool) (ns : Name)
    (openDecls : List OpenDecl) (ns0 : Name) (openDecls0 : List OpenDecl) :
    Environment → Name → List OpenDecl → Bool :=
  if ns == ns0 && openDecls == openDecls0 then
    if ns0.isAnonymous then fun env ns' od' => check env ns' od' && check env .anonymous od'
    else check
  else fun env ns' od' => ns' == ns0 && od' == openDecls0 && check env ns openDecls

private unsafe def toDepsImpl (accesses : Array EnvAccess) (checks : Array NonScalar) (ns0 : Name)
    (openDecls0 : List OpenDecl) : Deps := Id.run do
  let moduleUseExts := unsafeBaseIO moduleUseExtsRef.get
  let mut seen : Std.HashMap AccessKey Unit := {}
  let mut cs : Array (Environment → Name → List OpenDecl → Bool) := #[]
  let mut as : Array EnvAccess := #[]
  let mut ops : Array EnvAccess := #[]
  for a in accesses, c in checks do
    match a with
    | .cache .. => ops := ops.push a
    | _ =>
      if let .ext idx .. := a then
        if moduleUseExts.contains idx then continue
      let some key := accessKey a | continue
      unless seen.contains key do
        seen := seen.insert key ()
        let c := match a with
          | .resolve _ ns openDecls | .resolveNamespace _ ns openDecls =>
            resolutionCheck (unsafeCast c) ns (openDeclsOf openDecls) ns0 openDecls0
          | .scope _ => fun _ ns' od' => ns' == ns0 && od' == openDecls0
          | _ => unsafeCast c
        cs := cs.push c
        as := as.push a
  return { checks := cs, accesses := as, cacheOps := ops }

@[implemented_by toDepsImpl]
private opaque toDeps (accesses : Array EnvAccess) (checks : Array NonScalar) (ns0 : Name)
    (openDecls0 : List OpenDecl) : Deps

/-- Records a read of the current namespace and open declarations by `decl` otherwise than to
resolve a name, if this thread records (`EnvAccess.scope`), counting no heartbeats. -/
def recordScope (decl : Name) : BaseIO Unit := do
  let heartbeats ← IO.getNumHeartbeats
  envRecordAll #[.scope decl] #[unsafe unsafeCast ()]
  setHeartbeats heartbeats

/-- What a recording that ended usable recorded, from which `Raw.deps` makes its dependencies: only
when they are wanted, as most recordings of typeclass searches are never reused. -/
structure Raw where
  private accesses : Array EnvAccess
  private checks : Array NonScalar
  private ns : Name
  private openDecls : List OpenDecl

/-- The dependencies that `r` recorded. -/
def Raw.deps (r : Raw) : Deps :=
  toDeps r.accesses r.checks r.ns r.openDecls

/-- A recording in progress on this thread. -/
structure Recording where
  private before : Environment
  /-- The current namespace and open declarations at the start. -/
  private ns : Name
  private openDecls : List OpenDecl
  /-- The result once stopped. -/
  private result : IO.Ref (Option (Except String Raw))

/-- Starts recording this thread's accesses to the environment. -/
def start [Monad m] [MonadEnv m] [MonadResolveName m] [MonadLiftT BaseIO m] : m Recording := do
  let before ← getEnv
  let ns ← getCurrNamespace
  let openDecls ← getOpenDecls
  let result ← (IO.mkRef none : BaseIO _)
  (envStartRecording : BaseIO Unit)
  return { before, ns, openDecls, result }

/--
Ends the recording `r` (if it has not ended yet; it must be the one this thread started last): the
dependencies if the recording is usable and the environment, which is now `getEnv`, has changed only
by records of module uses, else why not.
-/
def Recording.stop [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] (r : Recording) :
    m (Except String Raw) := do
  if let some d ← (r.result.get : BaseIO _) then
    return d
  let (accesses, checks, why) ← (envStopRecording : BaseIO _)
  let after ← getEnv
  let moduleUseExts ← (moduleUseExtsRef.get : BaseIO _)
  let d := if !why.isEmpty then .error why
    else if unsafe ptrEq r.before after || sameBut r.before after moduleUseExts then
      .ok { accesses, checks, ns := r.ns, openDecls := r.openDecls }
    else .error "a change of the environment"
  (r.result.set (some d) : BaseIO Unit)
  return d

/-! The equality of expressions under which results are reused. -/

/-- Whether names are equal, or both inaccessible (with macro scopes) and equal without them. -/
def sameName (a b : Name) : Bool :=
  a == b || (a.hasMacroScopes && b.hasMacroScopes && a.eraseMacroScopes == b.eraseMacroScopes)

private unsafe def sameExprImpl (a b : Expr) : Bool :=
  (go a b |>.run' {}).run
where
  go (a b : Expr) : StateT (Std.HashMap (USize × USize) Unit) Id Bool := do
    if ptrEq a b then
      return true
    -- (`Expr.hash` covers neither binder names nor binder annotations)
    if a.hash != b.hash then
      return false
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
      modify (·.insert key ())
    return r

/-- Structural equality of expressions with equal binder kinds and binder names compared by
`sameName` (the macro scopes of inaccessible names differ from command to command). -/
@[implemented_by sameExprImpl]
opaque sameExpr (a b : Expr) : Bool

end Lean.PaperLean.EnvDeps
