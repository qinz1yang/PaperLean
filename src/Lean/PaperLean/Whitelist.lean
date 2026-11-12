/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lean.Environment
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.InitAttr
import Lean.PaperLean.Base

-- (no `SizeOf` instances for PaperLean's types: an instance of a module of `Lean` would be one of
-- every environment that imports it, which Lean's searches would try)
set_option genSizeOf false
set_option genInjectivity false

public section

/-!
The elaborators that are not Lean's own and that a recording may run (`Lean.PaperLean.EnvDeps`).

An entry of a `KeyedDeclsAttribute` other than `macro` that is not Lean's own makes a recording
unusable, and that is all that happens to it: nothing tells what such code reads. The exceptions are
the notations of Mathlib and its dependencies on the list below, without which much of what reuse
gains would be lost. They were taken by how many reuses they block over all of Mathlib, until what is
left is negligible.

Each was vetted once, by its source and its compiled code (its IR, and all of what that reaches but
Lean's own): it reads only what a recording sees, that is, the universe names, the local context and
its own syntax, and all else through Lean's functions, which record. It has no field of the
environment, no read of the namespace or open declarations of its own, no `evalConst`, no `IO`, no
global references. (`withTraceNode` reads the clock, for what it traces, and no recording is made with
trace options on.) An entry holds a hash of the code vetted (`codeHash`), so that another version of it
is simply not trusted.

To add an entry, or to vet a new version of one: read its source and its code, then take the hash that
`codeHash` gives in a file that imports it.
-/

namespace Lean.PaperLean.Whitelist

/-- An elaborator that a recording may run. -/
structure Entry where
  /-- The declaration of the attribute's entry. -/
  decl : Name
  /-- `codeHash` of the code vetted. -/
  hash : UInt64

/-- The list, the elaborators that block the most reuses first. -/
def entries : Array Entry := #[
  -- `Type*`: a fresh universe name, from the universe names alone.
  { decl := `Lean.Elab.Term.«_aux_Mathlib_Tactic_TypeStar___elabRules_Lean_Elab_Term_termType*_1»
    hash := 0x5a12507c9236a390 },
  -- `Category* C`: the same, after elaborating `C` with Lean's `elabTermEnsuringType`.
  { decl := `Mathlib.Tactic.CategoryStar.«_aux_Mathlib_Tactic_CategoryTheory_CategoryStar___elabRules_Mathlib_Tactic_CategoryStar_termCategory*___1»
    hash := 0x80d44555be325089 },
  -- `Sort*`: as `Type*`.
  { decl := `Lean.Elab.Term.«_aux_Mathlib_Tactic_TypeStar___elabRules_Lean_Elab_Term_termSort*_1»
    hash := 0xbeef68e6631a5875 },
  -- Qq's `Q(t)`: the local context and universe names, and Lean's `elabTerm`, `isDefEq` and searches.
  { decl := `Qq.«_aux_Qq_Macro___elabRules_Qq_termQ(__)_1_1»
    hash := 0x39d323f75ffcc91f },
  -- `TangentSpace% E`: finds a model in the local context and local instances, with Lean's `whnf`,
  -- `isDefEq`, `inferType`, `elabTerm` and searches.
  { decl := `Manifold.«_aux_Mathlib_Geometry_Manifold_Notation___elabRules_Manifold_termTangentSpace%___1»
    hash := 0x673842f93b993851 },
  -- `x ⊆ y`: Lean's `elabApp`, and a search for `UsesSetNotationForOrder`.
  { decl := `Mathlib.Meta.SetNotationForOrder.elabSubsetStx'
    hash := 0x6019124927ee1eb9 },
  -- `↧X`: `Environment.find?` of the head constant's `of`, and Lean's `elabTerm`.
  { decl := `CategoryTheory.«_aux_Mathlib_CategoryTheory_ConcreteCategory_Notation___elabRules_CategoryTheory_term↧__1»
    hash := 0x2191ba5ab1e6f369 }]

/-- Whether the declaration `n` is of a module of Lean, whose code records what it reads. -/
private def isLeans (env : Environment) (n : Name) : Bool :=
  (env.getModuleIdxFor? n).any fun i =>
    env.header.modules[i.toNat]?.any fun m =>
      let root := m.module.getRoot
      root == `Init || root == `Std || root == `Lean

private def mix (h : UInt64) (n : Nat) : UInt64 := mixHash h (hash n)

private def mixArgs (h : UInt64) (ys : Array IR.Arg) : UInt64 :=
  ys.foldl (init := mix h ys.size) fun h y => match y with
    | .var x => mix h (x.idx + 1)
    | .erased => mix h 0

private def mixCtor (h : UInt64) (i : IR.CtorInfo) : UInt64 :=
  mix (mix (mix (mix (mixHash h (hash i.name)) i.cidx) i.size) i.usize) i.ssize

private def mixExpr (h : UInt64) : IR.Expr → UInt64
  | .ctor i ys => mixArgs (mixCtor (mix h 1) i) ys
  | .reset n x => mix (mix (mix h 2) n) x.idx
  | .reuse x i _ ys => mixArgs (mixCtor (mix (mix h 3) x.idx) i) ys
  | .proj i x => mix (mix (mix h 4) i) x.idx
  | .uproj i x => mix (mix (mix h 5) i) x.idx
  | .sproj n o x => mix (mix (mix (mix h 6) n) o) x.idx
  | .fap c ys => mixArgs (mixHash (mix h 7) (hash c)) ys
  | .pap c ys => mixArgs (mixHash (mix h 8) (hash c)) ys
  | .ap x ys => mixArgs (mix (mix h 9) x.idx) ys
  | .box _ x => mix (mix h 10) x.idx
  | .unbox x => mix (mix h 11) x.idx
  | .lit (.num n) => mix (mix h 12) n
  | .lit (.str s) => mixHash (mix h 13) (hash s)
  | .isShared x => mix (mix h 14) x.idx

/-- `h` with what `b` does: all but its types and reference counts. -/
private partial def mixBody (h : UInt64) : IR.FnBody → UInt64
  | .vdecl x _ e b => mixBody (mixExpr (mix h x.idx) e) b
  | .jdecl j xs v b => mixBody (mixBody (mix (mix h j.idx) xs.size) v) b
  | .set x i y b => mixBody (mixArgs (mix (mix (mix h 21) x.idx) i) #[y]) b
  | .setTag x c b => mixBody (mix (mix (mix h 22) x.idx) c) b
  | .uset x i y b => mixBody (mix (mix (mix (mix h 23) x.idx) i) y.idx) b
  | .sset x i o y _ b => mixBody (mix (mix (mix (mix (mix h 24) x.idx) i) o) y.idx) b
  | .inc _ _ _ _ b | .dec _ _ _ _ b | .del _ b => mixBody h b
  | .case _ x _ cs => cs.foldl (init := mix (mix h 25) x.idx) fun h c => match c with
    | .ctor i b => mixBody (mixCtor h i) b
    | .default b => mixBody (mix h 26) b
  | .ret x => mixArgs (mix h 27) #[x]
  | .jmp j ys => mixArgs (mix (mix h 28) j.idx) ys
  | .unreachable => mix h 29

/-- `acc` with the functions that `b` calls. -/
private partial def callees (acc : NameSet) : IR.FnBody → NameSet
  | .vdecl _ _ (.fap c _) b | .vdecl _ _ (.pap c _) b => callees (acc.insert c) b
  | .jdecl _ _ v b => callees (callees acc v) b
  | .case _ _ _ cs => cs.foldl (fun acc c => callees acc c.body) acc
  | b => if b.isTerminal then acc else callees acc b.body

/-- The hash of the compiled code of `declName` and of all that it reaches, but Lean's own. -/
def codeHash (env : Environment) (declName : Name) : UInt64 := Id.run do
  let mut seen : NameSet := {}
  let mut todo := [declName]
  let mut h : UInt64 := 7
  while true do
    let n :: rest := todo | break
    todo := rest
    if seen.contains n || isLeans env n then continue
    seen := seen.insert n
    let some d := IR.findEnvDecl env n | continue
    h := mix (mixHash h (hash n)) d.params.size
    if let some f := getInitFnNameFor? env n then
      todo := f :: todo
    if let .fdecl (body := b) .. := d then
      h := mixBody h b
      todo := (callees {} b).toList ++ todo
  return h

/-- Whether each entry's code is the code vetted, with the header of the imports it was found for:
another environment of the process may import other code under the same module name and index. The
header is kept, so that its address, which identifies the imports, is not reused by another object. -/
private builtin_initialize vettedRef : IO.Ref (NameMap (EnvironmentHeader × Bool)) ← IO.mkRef {}

/-- Whether the code of `e`, imported in `env`, is the code vetted. An answer is used again only for
the imports it was found for; a declaration of the current module is never the code vetted. -/
private unsafe def isVetted (env : Environment) (e : Entry) : BaseIO Bool := do
  if (env.getModuleIdxFor? e.decl).isNone then
    return false
  let header := env.header
  if let some (header', r) := (← vettedRef.get).find? e.decl then
    if ptrEq header' header then
      return r
  let r := codeHash env e.decl == e.hash
  vettedRef.modify (·.insert e.decl (header, r))
  return r

/-- Whether the entry `declName` of an attribute is Lean's own. The entries of imported modules are
not builtin; those of the current module are, but their declarations are that module's. -/
private def isOwn (env : Environment) (declName : Name) (isBuiltin : Bool) : Bool :=
  isBuiltin && ((env.getModuleIdxFor? declName).isSome || !env.contains declName)

/-- Why a recording that runs the entry `declName` of an attribute is unusable, if it is. -/
private def refusal? (env : Environment) (declName : Name) (isBuiltin : Bool) : Option String :=
  envWithoutRecording fun _ =>
    if isOwn env declName isBuiltin then none else
    match entries.find? (·.decl == declName) with
    | none => some s!"the elaborator {declName}, not on the whitelist"
    | some e =>
      if unsafe unsafeBaseIO (isVetted env e) then none
      else some s!"the elaborator {declName}, whose code is not the code vetted"

/-- `r`, after making this thread's recording unusable if the entry `declName` of an attribute, which
the computation gets to run it, is neither Lean's own nor on the list. -/
def noteEntry {α : Type} (env : Environment) (declName : Name) (isBuiltin : Bool) (r : α) : α :=
  match refusal? env declName isBuiltin with
  | none => r
  | some why => envMarkUnusable why r

end Lean.PaperLean.Whitelist
