/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from Lean's LCNF converter.
-/
module
prelude
public import Lean.Meta.AppBuilder
import Init.While
import Lean.Compiler.InlineAttrs
import Lean.Compiler.CSimpAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Meta.Match.MatcherInfo

set_option genSizeOf false

public section
namespace Lean.PaperLean
open Compiler

/-- Only the key object allocated for this conversion can identify its internal
metadata. A retained annotation from another conversion may have the same spelling. -/
def macroMarker? (d : MData) (key : Name) : Option DataValue :=
  d.entries.findSome? fun (k, v) => if unsafe ptrEq k key then some v else none

/-- Remove a pre-existing field that merely spells the private key, preserving the rest
of its metadata. This also keeps structurally compared compiler cache keys distinct from
owned annotations. Only an actual collision needs a recursive visit of the wrapped term. -/
partial def prepareHeads (key : Name) (mark? : Name → Option MData) (body : Expr) : Expr :=
  body.replace fun e => match e with
    | .mdata d v =>
      if d.contains key && (macroMarker? d key).isNone then
        some (.mdata (d.erase key) (prepareHeads key mark? v))
      else none
    | .const n _ => (mark? n).map (.mdata · e)
    | _ => none

inductive ApplicationStep where
  | stop
  | alias (fn : Expr)
  | expand (value : Expr)

/-- The two kinds of pre-LCNF body expansion. -/
inductive BodyKind where
  | macroInline
  | matcher

def isMacroHead (env : Environment) (n : Name) : Bool :=
  hasMacroInlineAttribute env n || n == ``instDecidableAnd || n == ``instDecidableOr

def isMatcherHead (env : Environment) (n : Name) : Bool :=
  (Meta.getMatcherInfoCore? env n).isSome || Meta.isMatcherLikeCore env n

/-- The next rc3 pass for a computational reference. A macro or matcher opens a
body in its own pass; a body opened by LCNF conversion begins at the late replacement.
Settled eta heads have already consumed their replacement. Raw expansion is reserved
for a recursive CSimp macro with no standalone implementation. -/
inductive RewriteStage where
  | original | macros | matchers | finalMacros | late | settled | raw

def RewriteStage.tag : RewriteStage → Nat
  | .original => 0 | .macros => 1 | .matchers => 2 | .finalMacros => 3
  | .late => 4 | .settled => 5 | .raw => 6

def RewriteStage.read? (scope : MData) (key : Name) : Option RewriteStage :=
  match macroMarker? scope key with
  | some (.ofNat 0) => some .original
  | some (.ofNat 1) => some .macros
  | some (.ofNat 2) => some .matchers
  | some (.ofNat 3) => some .finalMacros
  | some (.ofNat 4) => some .late
  | some (.ofNat 5) => some .settled
  | some (.ofNat 6) => some .raw
  | _ => none

def RewriteStage.mark (stage : RewriteStage) (scope : MData) (key : Name) : MData :=
  scope.setNat key stage.tag

/-- An unchanged head cannot acquire a second macro opportunity between the two
macro passes. A matcher body, on the other hand, can introduce one. -/
def RewriteStage.body? (stage : RewriteStage) (env : Environment) (n : Name) :
    Option (BodyKind × RewriteStage) := Id.run do
  match stage with
  | .original | .macros =>
    if isMacroHead env n then return some (.macroInline, .macros)
    if isMatcherHead env n then return some (.matcher, .matchers)
  | .matchers =>
    if isMatcherHead env n then return some (.matcher, .matchers)
    if isMacroHead env n then return some (.macroInline, .finalMacros)
  | .finalMacros =>
    if isMacroHead env n then return some (.macroInline, .finalMacros)
  | .raw =>
    if isMacroHead env n then return some (.macroInline, .raw)
    if isMatcherHead env n then return some (.matcher, .raw)
  | .late | .settled => pure ()
  return none

/-- Mark the original references that participate in rc3's initial replacement pass.
Keep their actual constants in dependent types and erased proofs. After a macro body
has been opened, its new references participate only in the late replacement. -/
def markOriginalHeads (env : Environment) (key : Name) (value : Expr) : Expr := Id.run do
  let rules := (CSimp.ext.getState env).map
  let marker := RewriteStage.original.mark {} key
  return prepareHeads key (body := value) fun n => do
    guard <| (isUnsafeRecName? n).isSome || rules.contains n
    return marker

/-- Apply arguments just as `Expr.beta` does, except that the private annotation on a
constant must remain on the rebuilt application. Other metadata on the consumed lambda
spine stays transparent. Used for bodies, recursor minors, and proof overapplications. -/
def applyBody (body : Expr) (args : Array Expr) (key? : Option Name := none) : Expr :=
  match key? with
  | none => body.beta args
  | some key =>
    if args.isEmpty then body else
    let rev := args.reverse
    let finish := fun term i =>
      let remaining := rev.size - i
      mkAppRange (Expr.instantiateRange term remaining rev.size rev) i args.size args
    let rec go (term : Expr) (i : Nat) : Expr := match term with
      | .lam _ _ b _ =>
        if i + 1 < rev.size then go b (i + 1) else b.instantiate rev
      | .mdata d b =>
        if b.isConst && (macroMarker? d key).isSome then finish term i else go b i
      | _ => finish term i
    go body 0

/-- Expand just the requested kind of body. The caller owns pass ordering. -/
def expandApplication? (e : Expr) (kind : BodyKind) (prepareBody : Expr → Expr := id)
    (scopeKey? : Option Name := none) (etaHead? : Option Expr := none) : MetaM (Option Expr) :=
  e.withApp fun fn args => match kind with
    | .macroInline => macroInline fn args
    | .matcher => inlineMatcher e fn args
where
  macroInline (fn : Expr) (args : Array Expr) : MetaM (Option Expr) := do
    let .const declName us := fn | return none
    -- Keep the two rc3 instances callable as ordinary exported functions. At a use
    -- site their boolean right operand is evaluated only when the left one needs it.
    unless isMacroHead (← getEnv) declName do return none
    let val ← Core.instantiateValueLevelParams (← getConstInfo declName) us
    return some <| applyBody (prepareBody val) args scopeKey?

  inlineMatcher (e : Expr) (fn : Expr) (args : Array Expr) : MetaM (Option Expr) := do
    let .const declName us := fn | return none
    if let some info ← Meta.getMatcherInfo? declName then
      let numArgs := args.size
      if numArgs < info.arity then
        Meta.forallBoundedTelescope (← Meta.inferType e) (info.arity - numArgs) fun xs _ =>
          let original := match etaHead? with
            | some head => mkAppN head args
            | none => e
          return some (← Meta.mkLambdaFVars xs (mkAppN original xs))
      else
        let overappliedArgs := args[info.arity...*].toArray
        let mut args := args[0...info.arity].toArray
        let altNumParams := info.altNumParams
        let rec aux (i : Nat) (args : Array Expr) (letFVars : Array Expr) : MetaM Expr := do
          if h : i < altNumParams.size then
            let altIdx := i + info.getFirstAltPos
            let numParams := altNumParams[i]
            let alt ← normalizeAlt args[altIdx]! numParams
            Meta.withLetDecl (← mkFreshUserName `_alt) (← Meta.inferType alt) alt fun altFVar =>
              aux (i+1) (args.set! altIdx altFVar) (letFVars.push altFVar)
          else
            let info ← getConstInfo declName
            let value := applyBody (prepareBody (← Core.instantiateValueLevelParams info us)) args scopeKey?
            Meta.mkLetFVars letFVars value
        let inlined ← aux 0 args #[]
        return some <| mkAppN inlined overappliedArgs
    else if ← Meta.isMatcherLike declName then
      let info ← getConstInfo declName
      let value ← Core.instantiateValueLevelParams info us
      /-
      Currently the only declarations that are "matcher like" are `match_on_same_ctor.het`, for them
      each alternative is used uniquely so we can just beta reduce without introducing code
      duplication. If more "matcher like" things are introduced we might have to extend this with a
      generalized notion of matcher information.
      -/
      return some <| applyBody (prepareBody value) args scopeKey?
    else
      return none

  normalizeAlt (e : Expr) (numParams : Nat) : MetaM Expr :=
    Meta.lambdaTelescope e fun xs body => do
      if xs.size == numParams then
        return e
      else if xs.size > numParams then
        let body ← Meta.mkLambdaFVars xs[numParams...*] body
        let body ← Meta.withLetDecl (← mkFreshUserName `_k) (← Meta.inferType body) body fun x => Meta.mkLetFVars #[x] x
        Meta.mkLambdaFVars xs[*...numParams] body
      else
        Meta.forallBoundedTelescope (← Meta.inferType e) (numParams - xs.size) fun ys _ =>
          Meta.mkLambdaFVars (xs ++ ys) (mkAppN e ys)

/-- Inspect one computational application. A name replacement is separate from an expanded
body so a cycle of constant names can be closed without revisiting the same expression. -/
def applicationStep (e : Expr) (replaceAliases := true) (preferBody := false)
    (prepareBody : Expr → Expr := id) (scopeKey? : Option Name := none)
    (etaHead? : Option Expr := none) : MetaM ApplicationStep := do
  e.withApp fun fn _ => do
    if replaceAliases then
      if let .const n us := fn then
        if let some safe := isUnsafeRecName? n then return .alias (mkConst safe us)
    -- rc3 replaces the source constant before its macro and matcher passes. A
    -- replacement that is itself a macro or matcher is expanded by those passes.
    if replaceAliases && !preferBody then
      if let some target ← CSimp.replaceConstant? (← getEnv) fn then return .alias target
    if let some value ← expandApplication? e .matcher prepareBody scopeKey? etaHead? then return .expand value
    if let some value ← expandApplication? e .macroInline prepareBody scopeKey? etaHead? then return .expand value
    if replaceAliases && preferBody then
      if let some target ← CSimp.replaceConstant? (← getEnv) fn then return .alias target
    return .stop

def rewriteApplication (e : Expr) : MetaM (Option Expr) := do
  match ← applicationStep e with
  | .alias fn => return some (mkAppN fn e.getAppArgs)
  | .expand value => return some value
  | .stop => return none

end Lean.PaperLean
