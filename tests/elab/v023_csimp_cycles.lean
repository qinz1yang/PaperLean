@[noinline] def selfRule (n : Nat) := n + 1
@[csimp] theorem selfRule_eq : selfRule = selfRule := rfl
def useSelf (n : Nat) := selfRule n

@[noinline] def cycleLeft (n : Nat) := n + 1
@[noinline] def cycleRight (n : Nat) := n + 1
@[csimp] theorem leftToRight : cycleLeft = cycleRight := rfl
@[csimp] theorem rightToLeft : cycleRight = cycleLeft := rfl
def useCycle (n : Nat) := cycleLeft n

-- Lowering the replacement's macro body would return to the same source.
@[noinline] def cycleSource (n : Nat) := n + 1
@[macro_inline] def cycleAlias (n : Nat) := cycleSource n
@[csimp] theorem sourceToAlias : cycleSource = cycleAlias := rfl
def useAlias (n : Nat) := cycleSource n

-- The argument changes at every unfolding. An exact-expression guard alone would loop.
@[noinline] def growingSource (_n : Nat) : Nat := 7
@[noinline] def growingMiddle (_n : Nat) : Nat := 7
@[macro_inline] def growingAlias (n : Nat) := growingSource (n + 1)
@[csimp] theorem growing_step : growingSource = growingMiddle := rfl
@[csimp] theorem growing_eq : growingMiddle = growingAlias := rfl
def useGrowing (n : Nat) := growingSource n

/-- info: [2, 2, 2, 7] -/
#guard_msgs in
#eval [useSelf 1, useCycle 1, useAlias 1, useGrowing 1]

@[noinline] def hopA (n : Nat) := n
@[noinline] def hopB (n : Nat) := n
@[noinline] def hopC (n : Nat) := n
@[noinline] def hopD (n : Nat) := n
@[macro_inline] def exposedByMacro (n : Nat) := hopA n
@[csimp] theorem hopAB : hopA = hopB := rfl
@[csimp] theorem hopBC : hopB = hopC := rfl
@[csimp] theorem hopCD : hopC = hopD := rfl

-- An original reference takes one initial step and one late step.
/--
trace: [Compiler.init] size: 1
    def directHops n : Nat :=
      let _x.1 := hopC n;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.init true in
def directHops (n : Nat) := hopA n

-- A source first exposed by a macro has only its late step.
/--
trace: [Compiler.init] size: 1
    def exposedHop n : Nat :=
      let _x.1 := hopB n;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.init true in
def exposedHop (n : Nat) := exposedByMacro n

-- A macro exposed by a late CSimp must still choose the branch before evaluating it.
@[noinline] def chooseBranch (c : Bool) (t e : Nat) : Nat := if c then t else e
@[macro_inline] def chooseBranchMacro (c : Bool) (t e : Nat) : Nat := if c then t else e
@[csimp] theorem chooseBranch_eq : chooseBranch = chooseBranchMacro := rfl
@[macro_inline] def throughMacro (c : Bool) (t e : Nat) := chooseBranch c t e
@[noinline] def noisy (n : Nat) : Nat := dbg_trace "unexpected evaluation"; n
def lazyUse (n : Nat) : Nat := throughMacro true n (noisy n)
def siblingUses (n : Nat) : Nat :=
  throughMacro true n (noisy n) + throughMacro false (noisy n) n
def nestedUse (n : Nat) : Nat :=
  throughMacro true (throughMacro true n (noisy n)) (noisy n)
/-- info: [1, 4, 3] -/
#guard_msgs in
#eval [lazyUse 1, siblingUses 2, nestedUse 3]

-- The compiler also preserves laziness when a partially applied caller operand becomes
-- the function head inside the expanded body.
@[noinline] def callWhen (b : Bool) (f : Nat → Nat) (n : Nat) : Nat :=
  if b then f (noisy n) else 0
@[macro_inline] def callWhenMacro (b : Bool) (f : Nat → Nat) (n : Nat) : Nat :=
  if b then f (noisy n) else 0
@[csimp] theorem callWhen_eq : callWhen = callWhenMacro := rfl
@[macro_inline] def callThrough (b : Bool) (f : Nat → Nat) (n : Nat) := callWhen b f n
def higherOrderUse (n : Nat) := callThrough true (callThrough false id) n
/-- info: 0 -/
#guard_msgs in
#eval higherOrderUse 3

-- A macro reached by a CSimp step expands before its own CSimp step, also in a cycle.
namespace MixedAliases
@[noinline] def source (b : Bool) (x y : Nat) := if b then x else y
@[macro_inline] def lazyTarget (b : Bool) (x y : Nat) := if b then x else y
@[noinline] def strictTarget (b : Bool) (x y : Nat) := if b then x else y
@[csimp] theorem toLazy : source = lazyTarget := rfl
section
theorem toStrict : lazyTarget = strictTarget := rfl
attribute [local csimp] toStrict
def acyclic (n : Nat) := source true n (noisy n)
end
@[csimp] theorem back : lazyTarget = source := rfl
def cyclic (n : Nat) := source true n (noisy n)
/-- info: [7, 8] -/
#guard_msgs in
#eval [acyclic 7, cyclic 8]
end MixedAliases

-- A proof mentioning the source is not a recursive runtime call. Force the nested
-- occurrences through a wrapper as well, so both early and late alias paths are covered.
namespace ProofReference
@[noinline] def source (b : Bool) (x y : Nat) := if b then x else y
@[macro_inline] def target (b : Bool) (x y : Nat) :=
  have _proof : source b x y = source b x y := rfl
  if b then x else y
@[csimp] theorem replace : source = target := rfl
@[macro_inline] def wrapper (b : Bool) (x y : Nat) := source b x y
def early (n : Nat) := source true (source true n (noisy n)) n
def late (n : Nat) := wrapper true (wrapper true n (noisy n)) n
/-- info: [7, 8] -/
#guard_msgs in
#eval [early 7, late 8]
end ProofReference

-- Only original references get the initial CSimp pass. A macro first exposed by
-- a wrapper still expands before a replacement that would force an unused argument.
namespace ExposedMacro
@[macro_inline] def lazyTarget (b : Bool) (x y : Nat) := if b then x else y
@[noinline] def strictTarget (b : Bool) (x y : Nat) := if b then x else y
@[macro_inline] def wrapper (b : Bool) (x y : Nat) := lazyTarget b x y
@[csimp] theorem replace : lazyTarget = strictTarget := rfl
def use (n : Nat) := wrapper true n (noisy n)
/-- info: 7 -/
#guard_msgs in
#eval use 7
end ExposedMacro

-- A generated matcher can itself be a CSimp source. The replacement runs before
-- the matcher is inlined. Its trace distinguishes explicitly selecting the implementation.
namespace MatcherAlias
def choose (b : Bool) (t e : Nat) := match b with | true => t | false => e
@[noinline] def observed (b : Bool) : Bool := dbg_trace "matcher replacement"; b
@[noinline] def replacement (motive : Bool → Sort u) (b : Bool)
    (t : Unit → motive true) (e : Unit → motive false) : motive b :=
  choose.match_1 motive (observed b) t e
@[csimp] theorem replace : @choose.match_1 = @replacement := by
  funext m b t e
  cases b <;> rfl
def use (n : Nat) := choose.match_1 (fun _ => Nat) true (fun _ => n) (fun _ => n + 1)
/--
info: matcher replacement
---
info: 3
-/
#guard_msgs in
#eval use 3
end MatcherAlias

-- Every bare alias is macro-inline, and the argument grows when this late body
-- tries to expand itself. The acyclic raw declarations still provide a finite result.
namespace GrowingMacros
@[macro_inline] def leaf (_n : Nat) : Nat := 7
@[macro_inline] def step (n : Nat) : Nat := leaf (n + 1)
@[csimp] theorem forward : leaf = step := rfl
@[csimp] theorem back : step = leaf := rfl
@[macro_inline] def wrapper (n : Nat) := leaf n
def use (n : Nat) := wrapper n
/-- info: 7 -/
#guard_msgs in
#eval use 42
end GrowingMacros

-- Partial macro operands keep their caller behavior when used more than once.
namespace HigherMulti
@[noinline] def expensive (n : Nat) : Nat := dbg_trace "evaluated"; n
@[noinline] def both (b : Bool) (f : Nat → Nat) (n : Nat) := if b then f (expensive n) + f (expensive (n+1)) else 0
@[macro_inline] def bothM (b : Bool) (f : Nat → Nat) (n : Nat) := if b then f (expensive n) + f (expensive (n+1)) else 0
@[csimp] theorem convert : both = bothM := rfl
@[macro_inline] def via (b : Bool) (f : Nat → Nat) (n : Nat) := both b f n
set_option compiler.small 0 in
def nested (b : Bool) (n : Nat) := via true (via b id) n
/-- info: 0 -/
#guard_msgs in
#eval nested false 3
end HigherMulti

-- Eta expansion of a partial late matcher preserves the same decision as a full application.
namespace Eta
@[noinline] def source (motive : Bool → Sort u) (b : Bool)
    (t : Unit → motive true) (e : Unit → motive false) : motive b := MatcherAlias.choose.match_1 motive b t e
@[csimp] theorem sourceRule : @source.{u} = @MatcherAlias.choose.match_1.{u} := by
  funext m b t e
  cases b <;> rfl
@[macro_inline] def wrapper (_ : Unit) (motive : Bool → Sort u) := @source motive
@[noinline] def useFn (f : (b : Bool) → (Unit → Nat) → (Unit → Nat) → Nat) (n : Nat) : Nat :=
  f true (fun _ => n) (fun _ => n+1)
def under (n : Nat) := useFn (wrapper () (fun _ => Nat)) n
def full (n : Nat) := wrapper () (fun _ => Nat) true (fun _ => n) (fun _ => n+1)
/-- info: [7, 8] -/
#guard_msgs in
#eval [under 7, full 8]
end Eta

-- A computational replacement does not change the type of a binder or its erased proof.
namespace ErasedSource
@[macro_inline] def tag (n : Nat) := n
noncomputable def chosen (n : Nat) := Classical.choose (show ∃ m : Nat, m = n from ⟨n, rfl⟩)
@[csimp] theorem replace : tag = chosen := by
  funext n
  exact (Classical.choose_spec (show ∃ m : Nat, m = n from ⟨n, rfl⟩)).symm

def payload : (match tag 0 with | 0 => Int → Nat | _ => Unit) := fun i => i.natAbs
@[noinline] def eraseProof {α : Type} (x : α) (_ : x = x) := x
def use (i : Int) : Nat :=
  let f : (match tag 0 with | 0 => Int → Nat | _ => Unit) := payload
  (eraseProof f rfl) i
/-- info: 7 -/
#guard_msgs in
#eval use (-7)
end ErasedSource
