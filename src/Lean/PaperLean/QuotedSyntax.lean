/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lean.Environment
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.MetaAttr
import Lean.Compiler.NoncomputableAttr
import Lean.PaperLean.Base
import Lean.PaperLean.QuotedSyntaxHook

-- (no `SizeOf` instances for PaperLean's types; see `Lean.PaperLean.Base`)
set_option genSizeOf false
set_option genInjectivity false

public section

/-!
The `Syntax` value of a tactic constant of this module, such as the one that `declareTacticSyntax`
declares for an auto-param binder (`(h : p := by tac)`), read off its definition: its value is the
closed term that `quoteAutoTactic` builds from constructors and literals, and evaluating that term
gives exactly the `Syntax` that the term spells.

Lean evaluates such a constant with the interpreter (`evalSyntaxConstant`), which needs the
constant's compiled code: the IR declarations are in an extension whose state on another branch is
that of the complete environment (`declMapExt`, `AsyncMode.sync`), and with `Elab.async`, `compileDecls`
compiles only after all earlier declarations were checked. So a proof that applies a lemma of the
same file with an auto-param waits for the proofs of all declarations before it, which serializes
the proofs of such files. Reading the value needs only the constant's definition, which `addDecl`
publishes at once.

Only constants of this module are read so (imported ones are evaluated without waiting), not while
the thread records environment accesses (`Lean.PaperLean.EnvDeps`), only constants that `evalConst`
may evaluate at all (in a `module`, `meta` ones: its `evalCheckMeta`), and only
definitions of type `Syntax` without `implemented_by`, `extern` or `noncomputable`, whose value is
exactly of the form that `quoteAutoTactic` produces; for any other constant `none`, and the caller
evaluates it as before.
-/

namespace Lean.PaperLean.QuotedSyntax

/-- `PAPERLEAN_QUOTED_SYNTAX=0`: every tactic constant is evaluated (for comparisons). -/
builtin_initialize disabled : Bool ← return (← IO.getEnv "PAPERLEAN_QUOTED_SYNTAX") == some "0"

/-- `mkRawNatLit n` or `mkNatLit n`. -/
private def natLit? : Expr → Option Nat
  | .lit (.natVal n) => some n
  | .app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``Nat [])) (.lit (.natVal n)))
      (.app (.const ``instOfNatNat []) (.lit (.natVal m))) => if n == m then some n else none
  | _ => none

private def strLit? : Expr → Option String
  | .lit (.strVal s) => some s
  | _ => none

/-- The arity of `Lean.Name.mkStr1` ... `Lean.Name.mkStr8`. -/
private def mkStrArity? (n : Name) : Option Nat :=
  #[``Name.mkStr1, ``Name.mkStr2, ``Name.mkStr3, ``Name.mkStr4, ``Name.mkStr5, ``Name.mkStr6,
    ``Name.mkStr7, ``Name.mkStr8].findIdx? (· == n) |>.map (· + 1)

/-- A `Name` as `ToExpr Name` writes it. -/
private partial def name? (e : Expr) : Option Name :=
  match e with
  | .const ``Name.anonymous [] => some .anonymous
  | .app (.app (.const ``Name.str []) p) s => return .str (← name? p) (← strLit? s)
  | .app (.app (.const ``Name.num []) p) n => return .num (← name? p) (← natLit? n)
  | _ =>
    match e.getAppFn with
    | .const c [] => do
      let k ← mkStrArity? c
      let args := e.getAppArgs
      guard (args.size == k)
      args.foldlM (init := Name.anonymous) fun n a => return .str n (← strLit? a)
    | _ => none

/-- A list of elements of type `ty` as `ToExpr (List α)` writes it. -/
private partial def list? {α : Type} (ty : Expr) (elem : Expr → Option α) (e : Expr) : Option (List α) :=
  match e with
  | .app (.const ``List.nil [.zero]) t => if t == ty then some [] else none
  | .app (.app (.app (.const ``List.cons [.zero]) t) x) xs =>
    if t == ty then return (← elem x) :: (← list? ty elem xs) else none
  | _ => none

/-- A `Syntax.Preresolved` as `ToExpr Syntax.Preresolved` writes it. -/
private def preresolved? : Expr → Option Syntax.Preresolved
  | .app (.const ``Syntax.Preresolved.namespace []) n => return .namespace (← name? n)
  | .app (.app (.const ``Syntax.Preresolved.decl []) n) ls =>
    return .decl (← name? n) (← list? (.const ``String []) strLit? ls)
  | _ => none

/-- The `Syntax` that a term built by `quoteAutoTactic` evaluates to. -/
private partial def syntax? (e : Expr) : Option Syntax :=
  match e with
  | .app (.app (.app (.app (.const ``Syntax.ident []) (.const ``SourceInfo.none []))
      (.app (.const ``String.toRawSubstring []) s)) val) pre => do
    return .ident .none (← strLit? s).toRawSubstring (← name? val)
      (← list? (.const ``Syntax.Preresolved []) preresolved? pre)
  | .app (.app (.app (.const ``Syntax.node []) (.const ``SourceInfo.none [])) k) args => do
    return .node .none (← name? k) (← array? args #[])
  | .app (.const ``mkAtom []) val => return .atom .none (← strLit? val)
  | _ => none
where
  /-- `Array.push (... (Array.push Array.empty a₁) ...) aₙ` with the elements `aₙ, ..., a₁` given
  in `acc`, from the last one. -/
  array? (e : Expr) (acc : Array Syntax) : Option (Array Syntax) :=
    match e with
    | .app (.const ``Array.empty [.zero]) (.const ``Syntax []) => some acc.reverse
    | .app (.app (.app (.const ``Array.push [.zero]) (.const ``Syntax [])) a) x => do
      array? a (acc.push (← syntax? x))
    | _ => none

/--
The `Syntax` value of the constant `constName` of this module if it is a definition of type `Syntax`
without `implemented_by`, `extern` or `noncomputable` whose value is of the form that
`quoteAutoTactic` produces; otherwise `none`. The value is what evaluating the constant gives.
Callers reach it through `Lean.PaperLean.QuotedSyntaxHook` (`ofConstant?`).
-/
def decode? (env : Environment) (constName : Name) : Option Syntax := do
  guard !disabled
  -- (not while this thread records environment accesses: evaluating makes the recording unusable,
  -- `Lean.PaperLean.EnvDeps`, and the caller keeps doing so)
  guard !envRecording constName
  guard (env.getModuleIdxFor? constName).isNone
  let .defnInfo d ← env.find? constName | none
  -- `evalConstCheck`'s last-line meta check: a non-`meta` definition of a module is not
  -- evaluable at compile time, and this fast path must not turn that error into success.
  guard (Lean.getIRPhases env constName != .runtime)
  guard (d.levelParams.isEmpty && d.type == .const ``Syntax [] && d.safety == .safe)
  guard (Compiler.getImplementedBy? env constName).isNone
  guard !isExtern env constName
  -- (the tags of this branch, without waiting for the other branches: a definition is tagged
  -- `noncomputable` by the branch that declares it, which this one descends from, or by a failing
  -- `compileDecls`, which cannot fail on a term of the form `quoteAutoTactic` produces)
  guard !isNoncomputable env constName (asyncMode := .local)
  syntax? d.value

builtin_initialize ofConstantRef.set decode?

end Lean.PaperLean.QuotedSyntax
