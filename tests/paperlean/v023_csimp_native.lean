import Lean

-- All four source functions are the identity in Lean. Their native implementations
-- return distinct values, so a call to the wrong replacement is observable.
@[noinline] def nativeA (n : Nat) := n + 1
@[implemented_by nativeA] def hopA (n : Nat) := n
@[noinline] def nativeB (n : Nat) := n + 2
@[implemented_by nativeB] def hopB (n : Nat) := n
@[noinline] def nativeC (n : Nat) := n + 3
@[implemented_by nativeC] def hopC (n : Nat) := n
@[noinline] def nativeD (n : Nat) := n + 4
@[implemented_by nativeD] def hopD (n : Nat) := n
@[csimp] theorem ab : hopA = hopB := rfl
@[csimp] theorem bc : hopB = hopC := rfl
@[csimp] theorem cd : hopC = hopD := rfl

@[macro_inline] def expose (n : Nat) := hopA n
@[macro_inline] def applyTo (f : Nat → Nat) (n : Nat) := f n
@[noinline] def direct (n : Nat) := hopA n
@[noinline] def exposed (n : Nat) := expose n
@[noinline] def operand (n : Nat) := applyTo hopA n

-- A constructor selected by the late step is already resolved, including when eta
-- expansion is required. A rule on the constructor itself would return 99.
@[noinline] def first (n : Nat) := Nat.succ n
@[noinline] def asCtor (n : Nat) := Nat.succ n
@[noinline] def afterImpl (_ : Nat) := 99
@[implemented_by afterImpl] def afterCtor (n : Nat) := Nat.succ n
@[csimp] theorem firstAsCtor : first = asCtor := rfl
@[csimp] theorem ctorTarget : asCtor = Nat.succ := rfl
@[csimp] theorem pastCtor : Nat.succ = afterCtor := rfl
@[macro_inline] def exposeCtor (n : Nat) := asCtor n
@[noinline] def originalCtor (n : Nat) := first n
@[noinline] def exposedCtor (n : Nat) := exposeCtor n
@[noinline] def partialCtor := first

@[macro_inline] def fromCtor (n : Nat) := Nat.succ n
@[noinline] def directCtorSource (n : Nat) := Nat.succ n
@[noinline] def exposedCtorSource (n : Nat) := fromCtor n

@[extern "lean_nat_succ"] def external (n : @& Nat) := n
@[noinline] def beforeExternal (n : Nat) := n
@[noinline] def middleExternal (n : Nat) := n
@[csimp] theorem firstExternal : beforeExternal = middleExternal := rfl
@[csimp] theorem reachExternal : middleExternal = external := rfl
@[csimp] theorem pastExternal : external = hopD := rfl
@[macro_inline] def exposeExternal (n : Nat) := beforeExternal n
@[noinline] def directExternal (n : Nat) := beforeExternal n
@[noinline] def exposedExternal (n : Nat) := exposeExternal n

structure Box where
  val : Nat

@[noinline] def observeImpl (n : Nat) := n + 10
@[implemented_by observeImpl] def observe (n : Nat) := n
@[noinline] def beforeProj (box : Box) := box.val
@[noinline] def asProj (box : Box) := observe box.val
@[csimp] theorem firstProj : beforeProj = asProj := rfl
@[csimp] theorem reachProj : asProj = Box.val := rfl
@[macro_inline] def exposeProj (box : Box) := asProj box
@[noinline] def directProj (box : Box) := beforeProj box
@[noinline] def exposedProj (box : Box) := exposeProj box

namespace LateProjection
structure Packet where
  value : Nat

@[macro_inline] def body (p : Packet) := p.value
@[noinline] def plusTen (p : Packet) := p.value + 10
@[implemented_by plusTen] def selected (p : Packet) := p.value
@[noinline] def plusTwenty (p : Packet) := p.value + 20
@[implemented_by plusTwenty] def next (p : Packet) := p.value
@[noinline] def middle (p : Packet) := body p
@[noinline] def start (p : Packet) := middle p
@[csimp] theorem select : body = selected := rfl
@[csimp] theorem further : selected = next := rfl
@[csimp] theorem project : middle = Packet.value := rfl
@[csimp] theorem initial : start = middle := rfl
@[macro_inline] def expose (p : Packet) := middle p

-- The projection opens middle's body during lowering. Its macro receives just
-- one late replacement, even though the same macro in original source takes two.
@[noinline] def direct (p : Packet) := start p
@[noinline] def exposed (p : Packet) := expose p
@[noinline] def original (p : Packet) := body p

def choose (b : Bool) (t e : Nat) := match b with | true => t | false => e
@[noinline] def flip (b : Bool) := !b
@[implemented_by flip] def seen (b : Bool) := b
@[noinline] def chosen (motive : Bool → Sort u) (b : Bool)
    (t : Unit → motive true) (e : Unit → motive false) : motive b :=
  choose.match_1 motive (seen b) t e
@[noinline] def applyMatcher (f : (b : Bool) → (Unit → Nat) → (Unit → Nat) → Nat)
    (p : Packet) := f true (fun _ => p.value) (fun _ => 17)
@[noinline] def fullBody (p : Packet) :=
  choose.match_1 (fun _ => Nat) true (fun _ => p.value) (fun _ => 17)
@[noinline] def partialBody (p : Packet) := applyMatcher (choose.match_1 (fun _ => Nat)) p
@[csimp] theorem matchRule : @choose.match_1 = @chosen := by
  funext m b t e
  cases b <;> rfl
@[csimp] theorem fullRule : fullBody = Packet.value := rfl
@[csimp] theorem partialRule : partialBody = Packet.value := rfl
@[macro_inline] def fullVia (p : Packet) := fullBody p
@[macro_inline] def partialVia (p : Packet) := partialBody p
@[noinline] def full (p : Packet) := fullVia p
@[noinline] def partialUse (p : Packet) := partialVia p
-- A matcher can expose a macro in its body. A matcher first revealed by that
-- final macro is already past matcher expansion, so its late rule selects chosen.
@[macro_inline] def indirect (motive : Bool → Sort u) (b : Bool)
    (t : Unit → motive true) (e : Unit → motive false) : motive b :=
  choose.match_1 motive b t e
def custom.match_a (motive : Bool → Sort u) (b : Bool)
    (t : Unit → motive true) (e : Unit → motive false) : motive b :=
  indirect motive b t e
run_meta do
  let some info ← Lean.Meta.getMatcherInfo? ``choose.match_1 | throwError "missing matcher info"
  Lean.Meta.Match.addMatcherInfo ``custom.match_a info
@[noinline] def afterFinalMacro (n : Nat) :=
  custom.match_a (fun _ => Nat) true (fun _ => n) (fun _ => 17)

@[macro_inline] def plainMacro (p : Packet) := p.value
@[noinline] def observed (p : Packet) : Nat := dbg_trace "late replacement"; p.value
@[noinline] def plainSource (p : Packet) := plainMacro p
@[csimp] theorem plainSelect : plainMacro = observed := by funext p; rfl
@[csimp] theorem plainProject : plainSource = Packet.value := rfl
@[macro_inline] def plainExpose (p : Packet) := plainSource p
@[noinline] def plainUse (p : Packet) := plainExpose p
/--
info: late replacement
---
info: 5
-/
#guard_msgs in
#eval plainUse ⟨5⟩


-- These bodies are bare constants. One also has a transparent elaborator annotation, and
-- the projection is overapplied since the selected field itself returns a function.
structure Callback where
  invoke : (Nat → Nat) → Nat
@[macro_inline] def projected (p : Callback) := p.invoke
@[noinline] def callImpl (_ : Callback) (f : Nat → Nat) := f 10
@[implemented_by callImpl] def callAt (p : Callback) := p.invoke
@[csimp] theorem chooseCall : projected = callAt := rfl
elab "notedProjected" : term =>
  pure <| Lean.Expr.mdata (Lean.KVMap.empty.setBool `test.annotation true) (Lean.mkConst ``projected)
@[noinline] def bare : Callback → (Nat → Nat) → Nat := projected
@[noinline] def noted : Callback → (Nat → Nat) → Nat := notedProjected
@[csimp] theorem bareRule : bare = Callback.invoke := rfl
@[csimp] theorem notedRule : noted = Callback.invoke := rfl
@[macro_inline] def viaBare (p : Callback) (f : Nat → Nat) := bare p f
@[macro_inline] def viaNoted (p : Callback) (f : Nat → Nat) := noted p f
@[noinline] def bareUse (p : Callback) := viaBare p (fun n => hopA n)
@[noinline] def notedUse (p : Callback) := viaNoted p (fun n => hopA n)

@[macro_inline] def minor (_ : True) (_ : True) : Nat := 5
@[noinline] def chosenMinor (_ : True) (_ : True) : Nat := dbg_trace "recursor replacement"; 5
@[csimp] theorem chooseMinor : minor = chosenMinor := by funext a b; rfl
@[noinline] def useMinor (h : True ∧ True) : Nat := And.rec minor h
/--
info: recursor replacement
---
info: 5
-/
#guard_msgs in
#eval useMinor ⟨trivial, trivial⟩

@[macro_inline] def alternative (_ : True) : Nat := 5
@[noinline] def chosenAlt (_ : True) : Nat := dbg_trace "alternative replacement"; 5
@[csimp] theorem chooseAlt : alternative = chosenAlt := by funext h; rfl
@[noinline] def overCases (b : Bool) (h : True) : Nat :=
  @Bool.casesOn (fun _ => True → Nat) b alternative alternative h
/--
info: alternative replacement
---
info: 5
-/
#guard_msgs in
#eval overCases true trivial
end LateProjection

def main : IO Unit := do
  let results := [direct 100, exposed 100, operand 100,
    originalCtor 4, exposedCtor 4, partialCtor 4, directCtorSource 4, exposedCtorSource 4,
    directExternal 100, exposedExternal 100, directProj ⟨5⟩, exposedProj ⟨7⟩,
    LateProjection.direct ⟨5⟩, LateProjection.exposed ⟨5⟩, LateProjection.original ⟨5⟩,
    LateProjection.full ⟨5⟩, LateProjection.partialUse ⟨5⟩, LateProjection.afterFinalMacro 5,
    LateProjection.bareUse ⟨fun f => f 1⟩, LateProjection.notedUse ⟨fun f => f 1⟩]
  unless results == [103, 102, 103, 5, 5, 5, 99, 99, 101, 100, 15, 17, 15, 15, 25, 17, 17, 17, 13, 13] do
    throw <| IO.userError s!"unexpected CSimp implementations: {results}"
