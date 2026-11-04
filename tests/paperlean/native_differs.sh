# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that native libraries of packages (`src/paperlean/native_libs.cpp`) are not used where their
# code differs from interpreting it, while other modules keep theirs:
# - a nullary constant whose evaluation has effects (a reference, the time, `dbgTrace`, a panic, also in
#   Lean's library or a primitive of the runtime), which native code evaluates once per process and the
#   interpreter in each of its runs, or a closed term in a function that does; a token for `IO` code
#   may come from anywhere that can give one a value;
# - what a primitive gets back from a closure and gives to the next one counts, and what cannot be
#   told of the flow of closures counts as an effect;
# - a library with a symbol that nothing defines, which fails to load instead of killing the process
#   at the first call.

cp native_helper.lean "$TMP_DIR/"
SRC="$TMP_DIR/src"
LIB="$TMP_DIR/lib"
mkdir -p "$SRC" "$LIB"
cd "$SRC"

cat > "$TMP_DIR/pack.lean" <<'END'
import Lean.PaperLean.OLeanPack
def main (args : List String) : IO Unit := do
  let n ← Lean.PaperLean.OLeanPack.create #[args[1]!] args[0]!
  IO.println s!"packed: {decide (n > 0)}"
END
# `build <module>...`: a library of the modules, with its manifest, and a pack of all modules so far
build() {
  local cs=()
  for m in "$@"; do
    run env LEAN_PATH="$LIB" lean -o "$LIB/$m.olean" -i "$LIB/$m.ilean" -c "$TMP_DIR/$m.c" $m.lean
    cs+=("$TMP_DIR/$m.c")
  done
  run leanc -shared -DLEAN_EXPORTING -o "$TMP_DIR/lib$1.so" "${cs[@]}"
  run env LEAN_PATH="$LIB" lean --run "$TMP_DIR/native_helper.lean" manifest "$TMP_DIR/lib$1.paperlean" "$TMP_DIR/lib$1.so" "$TMP_DIR" "$@"
  rm -f "$TMP_DIR/all.paperlean"
  capture lean --run "$TMP_DIR/pack.lean" "$TMP_DIR/all.paperlean" "$LIB"
  check_out_contains "packed: true"
}
# `native <manifest module> <file>`: `lean` on the file with the library
native() {
  capture env LEAN_BACKTRACE=0 LEAN_PATH="$LIB" LEAN_OLEAN_PACK="$TMP_DIR/all.paperlean" \
    PAPERLEAN_NATIVE_LIBS="$TMP_DIR/lib$1.paperlean" PAPERLEAN_IMPORT_TIMING=1 lean "$2"
}
# `same_as_plain <file>`: the output of `native` is that of `lean` without packs and libraries
same_as_plain() {
  grep -v "^paperlean-" "$CAPTURED.out.produced" > "$TMP_DIR/native.out" || true
  capture env LEAN_BACKTRACE=0 LEAN_PATH="$LIB" lean "$1"
  $DIFF -- "$CAPTURED.out.produced" "$TMP_DIR/native.out" || fail "$1 differs with the native library"
}

# Each module with one kind of effect in a constant, and what each run of the interpreter shows.
cat > Ref.lean <<'END'
unsafe def ctrImpl : IO.Ref Nat := unsafeBaseIO (IO.mkRef 0)
@[implemented_by ctrImpl] opaque ctr : IO.Ref Nat
def bump : IO Nat := do ctr.modify (· + 1); ctr.get
END
cat > UseRef.lean <<'END'
import Ref
#eval bump
#eval bump
END
build Ref
native Ref UseRef.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
same_as_plain UseRef.lean

# a closed term in a function, which native code also evaluates once per process
cat > Closed.lean <<'END'
unsafe def freshImpl (_ : Unit) : IO.Ref Nat := unsafeBaseIO (IO.mkRef 0)
@[implemented_by freshImpl] opaque fresh (u : Unit) : IO.Ref Nat
def bumpFresh : IO Nat := do let r := fresh (); r.modify (· + 1); r.get
END
cat > UseClosed.lean <<'END'
import Closed
#eval bumpFresh
#eval bumpFresh
END
build Closed
native Closed UseClosed.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
same_as_plain UseClosed.lean

cat > Trace.lean <<'END'
def noisy : Nat := dbgTrace "Trace.noisy evaluated" fun _ => 5
def trace1 (n : Nat) : Nat := n + 1
END
cat > UseTrace.lean <<'END'
import Trace
#eval trace1 1
END
build Trace
native Trace UseTrace.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
same_as_plain UseTrace.lean

cat > Panics.lean <<'END'
def boom : Nat := panic! "Panics.boom evaluated"
def panics1 (n : Nat) : Nat := n + 1
END
cat > UsePanics.lean <<'END'
import Panics
#eval panics1 1
END
build Panics
native Panics UsePanics.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
same_as_plain UsePanics.lean

# a closure that a primitive runs
cat > Thunks.lean <<'END'
def lazyNoisy : Nat := (Thunk.mk fun _ => dbgTrace "Thunks.lazyNoisy evaluated" fun _ => 5).get
def thunks1 (n : Nat) : Nat := n + 1
END
cat > UseThunks.lean <<'END'
import Thunks
#eval thunks1 1
END
build Thunks
native Thunks UseThunks.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
same_as_plain UseThunks.lean

# a closure that runs later: native code keeps the thunk of the constant for all runs
cat > Kept2.lean <<'END'
def keptThunk : Thunk Nat := Thunk.mk fun _ => dbgTrace "Kept2.keptThunk forced" fun _ => 5
@[noinline] def force (t : Thunk Nat) (n : Nat) : Nat := t.get + n
def forced (n : Nat) : Nat := force keptThunk n
END
cat > UseKept2.lean <<'END'
import Kept2
#eval forced 1
#eval forced 2
END
build Kept2
native Kept2 UseKept2.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
same_as_plain UseKept2.lean

# `runST` makes a world token, as a package's `unsafe` code can with `unsafeCast`
cat > Worlds.lean <<'END'
def viaST : Nat := runST fun _ => do
  let r ← ST.Prim.mkRef 0
  ST.Prim.Ref.modify r (· + 1)
  ST.Prim.Ref.get r
END
cat > UseWorlds.lean <<'END'
import Worlds
#eval viaST
END
build Worlds
native Worlds UseWorlds.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
same_as_plain UseWorlds.lean
cat > Casts.lean <<'END'
unsafe def myRun (fn : BaseIO α) : α :=
  match fn (unsafeCast Unit.unit) with
  | .mk a _ => a
unsafe def myRefImpl : IO.Ref Nat := myRun (IO.mkRef 0)
@[implemented_by myRefImpl] opaque myRef : IO.Ref Nat
def bumpMine : IO Nat := do myRef.modify (· + 1); myRef.get
END
cat > UseCasts.lean <<'END'
import Casts
#eval bumpMine
#eval bumpMine
END
build Casts
native Casts UseCasts.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
same_as_plain UseCasts.lean

# Tokens are not recognized by their shape: `unsafe` code that may make one, however it does, and a
# closure that takes one do not use native code, whatever the token is computed by.
cat > Tokens.lean <<'END'
@[noinline] def token (n : Nat) : Nat := n + 1
unsafe def viaResult (fn : BaseIO α) : α :=
  match fn (unsafeCast (token 1)) with
  | .mk a _ => a
unsafe def ref1Impl : IO.Ref Nat := viaResult (IO.mkRef 0)
@[implemented_by ref1Impl] opaque ref1 : IO.Ref Nat
def bump1 : IO Nat := do ref1.modify (· + 1); ref1.get
END
cat > UseTokens.lean <<'END'
import Tokens
#eval bump1
#eval bump1
END
build Tokens
native Tokens UseTokens.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
same_as_plain UseTokens.lean
cat > Aliases.lean <<'END'
@[noinline] def token (n : Nat) : Nat := n + 1
unsafe def viaAlias (fn : BaseIO α) (n : Nat) : α :=
  let t := token n
  let u := (t, t).1
  match fn (unsafeCast u) with
  | .mk a _ => a
unsafe def ref2Impl : IO.Ref Nat := viaAlias (IO.mkRef 0) 1
@[implemented_by ref2Impl] opaque ref2 : IO.Ref Nat
def bump2 : IO Nat := do ref2.modify (· + 1); ref2.get
END
cat > UseAliases.lean <<'END'
import Aliases
#eval bump2
#eval bump2
END
build Aliases
native Aliases UseAliases.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
same_as_plain UseAliases.lean
# the application is in a safe polymorphic function that knows of no token
cat > Helpers.lean <<'END'
@[noinline] def token (n : Nat) : Nat := n + 1
@[noinline] def apply {β γ : Type} (f : β → γ) (b : β) : γ := f b
unsafe def viaHelper (fn : BaseIO α) : α :=
  match apply fn (unsafeCast (token 1)) with
  | .mk a _ => a
unsafe def ref3Impl : IO.Ref Nat := viaHelper (IO.mkRef 0)
@[implemented_by ref3Impl] opaque ref3 : IO.Ref Nat
def bump3 : IO Nat := do ref3.modify (· + 1); ref3.get
END
cat > UseHelpers.lean <<'END'
import Helpers
#eval bump3
#eval bump3
END
build Helpers
native Helpers UseHelpers.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
same_as_plain UseHelpers.lean
# `unsafe` code that is inlined into a safe declaration leaves no trace of itself
cat > Inlined.lean <<'END'
@[noinline] def token (n : Nat) : Nat := n + 1
@[inline] unsafe def runImpl (n : Nat) (fn : BaseIO (IO.Ref Nat)) : IO.Ref Nat :=
  match fn (unsafeCast (token n)) with
  | .mk a _ => a
@[implemented_by runImpl] opaque run (n : Nat) (fn : BaseIO (IO.Ref Nat)) : IO.Ref Nat
@[noinline] def viaSafe (n : Nat) (f : BaseIO (IO.Ref Nat)) : IO.Ref Nat := run n f
def ref6 : IO.Ref Nat := viaSafe 1 (IO.mkRef 0)
def bump6 : IO Nat := do ref6.modify (· + 1); ref6.get
END
cat > UseInlined.lean <<'END'
import Inlined
#eval bump6
#eval bump6
END
build Inlined
native Inlined UseInlined.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
same_as_plain UseInlined.lean
# the closure goes through a structure and back
cat > Stored.lean <<'END'
@[noinline] def token (n : Nat) : Nat := n + 1
structure Box where
  act : BaseIO (IO.Ref Nat)
  n : Nat
@[noinline] def mkBox (act : BaseIO (IO.Ref Nat)) : Box := { act, n := 1 }
@[inline] unsafe def runImpl (b : Box) : IO.Ref Nat :=
  let w := token b.n
  match b.act (unsafeCast w) with
  | .mk a _ => a
@[implemented_by runImpl] opaque run (b : Box) : IO.Ref Nat
@[noinline] def viaSafe (b : Box) : IO.Ref Nat := run b
def ref7 : IO.Ref Nat := viaSafe (mkBox (IO.mkRef 0))
def bump7 : IO Nat := do ref7.modify (· + 1); ref7.get
END
cat > UseStored.lean <<'END'
import Stored
#eval bump7
#eval bump7
END
build Stored
native Stored UseStored.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
same_as_plain UseStored.lean
# what a primitive holds is found in all fields of a structure, whatever is in the others
cat > Hidden.lean <<'END'
@[noinline] def token (n : Nat) : Nat := n + 1
structure Holder where
  n : Nat
  act : BaseIO (IO.Ref Nat)
@[noinline] def holders (a : BaseIO (IO.Ref Nat)) (n : Nat) : Array Holder := #[{ n := 0, act := a }].push { n, act := a }
@[inline] unsafe def runImpl (h : Array Holder) (n : Nat) : IO.Ref Nat :=
  match h[n]? with
  | some x => match x.act (unsafeCast (token n)) with
    | .mk a _ => a
  | none => unsafeCast ()
@[implemented_by runImpl] opaque run (h : Array Holder) (n : Nat) : IO.Ref Nat
@[noinline] def viaSafe (h : Array Holder) (n : Nat) : IO.Ref Nat := run h n
def ref8 : IO.Ref Nat := viaSafe (holders (IO.mkRef 0) 1) 0
def bump8 : IO Nat := do ref8.modify (· + 1); ref8.get
END
cat > UseHidden.lean <<'END'
import Hidden
#eval bump8
#eval bump8
END
build Hidden
native Hidden UseHidden.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
same_as_plain UseHidden.lean
# no `unsafe` at all: an `IO` action can return its token, and `initialize` keeps it
cat > Kept.lean <<'END'
def getTok : BaseIO (Void IO.RealWorld) := fun w => .mk w w
initialize tok : Void IO.RealWorld ← getTok
def runIt (fn : BaseIO α) : α := match fn tok with | .mk a _ => a
def ref4 : IO.Ref Nat := runIt (IO.mkRef 0)
def bump4 : IO Nat := do ref4.modify (· + 1); ref4.get
END
cat > UseKept.lean <<'END'
import Kept
#eval bump4
#eval bump4
END
build Kept
native Kept UseKept.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
same_as_plain UseKept.lean

# A panic counts wherever it is: in Lean's library, in a runtime primitive, when nothing uses the
# constant. What is reachable but does not fire does not stop native code.
cat > LibPanic.lean <<'END'
def notUsed : Nat := "x".toNat!
def libPanic1 (n : Nat) : Nat := n + 1
END
cat > UseLibPanic.lean <<'END'
import LibPanic
#eval libPanic1 1
END
build LibPanic
native LibPanic UseLibPanic.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
! grep -q PANIC "$CAPTURED.out.produced" || fail "importing evaluated a constant that panics"
same_as_plain UseLibPanic.lean
cat > ArrPanic.lean <<'END'
def outOfRange : Nat := #[1, 2][5]!
def arrPanic1 (n : Nat) : Nat := n + 1
END
cat > UseArrPanic.lean <<'END'
import ArrPanic
#eval arrPanic1 1
END
build ArrPanic
native ArrPanic UseArrPanic.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
! grep -q PANIC "$CAPTURED.out.produced" || fail "importing evaluated a constant that panics"
same_as_plain UseArrPanic.lean
# in a closed term of a function that nothing calls
cat > ClosedPanic.lean <<'END'
def inFunction (n : Nat) : Nat := n + "y".toNat!
def closedPanic1 (n : Nat) : Nat := n + 1
END
cat > UseClosedPanic.lean <<'END'
import ClosedPanic
#eval closedPanic1 1
#eval inFunction 1
#eval inFunction 1
END
build ClosedPanic
native ClosedPanic UseClosedPanic.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
same_as_plain UseClosedPanic.lean
cat > Fires.lean <<'END'
def goodNat : Nat := "12".toNat!
def goodAssert : Nat := assert! (goodNat == 12); goodNat + 1
def goodGet : Nat := #[1, 2][1]!
def fires1 (n : Nat) : Nat := n + goodAssert + goodGet
END
cat > UseFires.lean <<'END'
import Fires
#eval fires1 1
END
build Fires
native Fires UseFires.lean
check_out_contains "paperlean-timing native libs=1 modules=1"
same_as_plain UseFires.lean

# An `[init]` value decides whether a constant panics. That of `register_option` is a function of
# constants: the evaluation decides, and it is the same in every run, ...
cat > Opts.lean <<'END'
import Lean.Data.Options
open Lean
initialize myOpt : Lean.Option Bool ← Option.register `my.opt { defValue := false, descr := "d" }
def okPart : Nat := #[1, 2, 3][myOpt.name.getNumParts]!
def opts1 (n : Nat) : Nat := n + okPart
END
cat > UseOpts.lean <<'END'
import Opts
#eval opts1 1
END
build Opts
native Opts UseOpts.lean
check_out_contains "paperlean-timing native libs=1 modules=1"
same_as_plain UseOpts.lean
cat > PureInit.lean <<'END'
initialize idx : Nat ← pure 5
def pickIt : Nat := #[1, 2][idx]!
def pureInit1 (n : Nat) : Nat := n + 1
END
cat > UsePureInit.lean <<'END'
import PureInit
#eval pureInit1 1
END
build PureInit
native PureInit UsePureInit.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
same_as_plain UsePureInit.lean
# ... but not for one that reads anything else, or handles an error, as what happens then can differ
cat > TimeInit.lean <<'END'
initialize idx : Nat ← do return (← IO.monoMsNow) % 2
def pickTime : Nat := #[1, 2][idx]!
def timeInit1 (n : Nat) : Nat := n + 1
END
cat > UseTimeInit.lean <<'END'
import TimeInit
#eval timeInit1 1
END
build TimeInit
native TimeInit UseTimeInit.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
same_as_plain UseTimeInit.lean
cat > CatchInit.lean <<'END'
import Lean.Data.Options
open Lean
initialize idx : Nat ← do
  try
    let o : Lean.Option Bool ← Option.register `my.caught { defValue := false, descr := "d" }
    return o.name.toString.length
  catch _ => return 100
def pickCaught : Nat := #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10][idx]!
def catchInit1 (n : Nat) : Nat := n + 1
END
cat > UseCatchInit.lean <<'END'
import CatchInit
#eval catchInit1 1
END
build CatchInit
native CatchInit UseCatchInit.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
same_as_plain UseCatchInit.lean

# A package's own `Lean.registerOption`, in a module that does not import Lean's, is no such thing.
cat > FakeOption.lean <<'END'
def Lean.registerOption (_ : Unit) : IO Nat := do return (← IO.monoMsNow) % 2
initialize idx : Nat ← Lean.registerOption ()
def pickFake : Nat := #[1, 2][idx]!
def fakeOption1 (n : Nat) : Nat := n + 1
END
cat > UseFakeOption.lean <<'END'
import FakeOption
#eval fakeOption1 1
END
build FakeOption
native FakeOption UseFakeOption.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
same_as_plain UseFakeOption.lean

# A primitive that runs a closure runs what is in it.
cat > InPrimitive.lean <<'END'
def anyNoisy : Bool := String.Internal.any "ab" fun _ => dbgTrace "InPrimitive.anyNoisy" fun _ => true
def inPrimitive1 (n : Nat) : Nat := n + 1
END
cat > UseInPrimitive.lean <<'END'
import InPrimitive
#eval inPrimitive1 1
END
build InPrimitive
native InPrimitive UseInPrimitive.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
same_as_plain UseInPrimitive.lean
# What a primitive gets back from a closure goes into what it gives the next one, which can apply it:
# the first call of `String.Internal.foldl`'s closure returns a closure, and the second applies it.
cat > FoldRef.lean <<'END'
unsafe def ctrImpl : IO.Ref Nat := unsafeCast <|
  String.Internal.foldl
    (fun s c => if c == 'a' then
        unsafeCast (fun (n : Nat) => (unsafeCast (unsafeBaseIO (IO.mkRef n)) : String))
      else (unsafeCast s : Nat → String) 0)
    "" "ab"
@[implemented_by ctrImpl] opaque foldCtr : IO.Ref Nat
def foldBump : IO Nat := do foldCtr.modify (· + 1); foldCtr.get
END
cat > UseFoldRef.lean <<'END'
import FoldRef
#eval foldBump
#eval foldBump
END
cat > FoldProof.lean <<'END'
import Lean
import FoldRef
#eval foldBump
open Lean Elab Tactic in
elab "rfl_after_counter" : tactic => do
  let n ← foldBump
  if n < 2 then throwError "not warmed up"
  evalTactic (← `(tactic| rfl))
theorem t : 2 = 2 := by rfl_after_counter
#print axioms t
END
build FoldRef
native FoldRef UseFoldRef.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
same_as_plain UseFoldRef.lean
[ "$(cat "$TMP_DIR/native.out")" = "$(printf '1\n1')" ] || fail "FoldRef's counter is shared by the runs"
for mode in "" PAPERLEAN_EXACT=1; do
  capture_exit 1 env $mode LEAN_BACKTRACE=0 LEAN_PATH="$LIB" LEAN_OLEAN_PACK="$TMP_DIR/all.paperlean" \
    PAPERLEAN_NATIVE_LIBS="$TMP_DIR/libFoldRef.paperlean" PAPERLEAN_IMPORT_TIMING=1 lean FoldProof.lean
  check_out_contains "not warmed up"
  check_out_contains "paperlean-timing native libs=0 modules=0"
  if grep -q "does not depend on any axioms" "$CAPTURED.out.produced"; then
    fail "FoldProof.lean is accepted"
  fi
done

# `foldl` as a closure, and the shapes that what comes back can have: in a structure or an array, as a
# closure of a closure, and what a closure that wants more arguments than a primitive gives holds.
cat > FoldTrace.lean <<'END'
namespace FoldTrace
unsafe def noiseImpl : String :=
  String.Internal.foldl
    (fun s c => if c == 'a' then unsafeCast (fun (_ : Unit) => dbgTrace "FoldTrace effect" fun _ => "result")
      else (unsafeCast s : Unit → String) ())
    "" "ab"
@[implemented_by noiseImpl] opaque noise : String
end FoldTrace
def foldtrace1 (n : Nat) : Nat := n + 1
END
cat > FoldIndirect.lean <<'END'
namespace FoldIndirect
@[noinline, nospecialize] def applyFold (f : (String → Char → String) → String → String → String)
    (g : String → Char → String) : String := f g "" "x"
def noise : String := applyFold String.Internal.foldl
  (fun s c => dbgTrace "FoldIndirect effect" fun _ => s.push c)
end FoldIndirect
def foldindirect1 (n : Nat) : Nat := n + 1
END
cat > FoldPair.lean <<'END'
namespace FoldPair
unsafe def noiseImpl : String :=
  String.Internal.foldl
    (fun s c => if c == 'a' then
        let p : (Unit → String) × Nat := (fun _ => dbgTrace "FoldPair effect" fun _ => "x", 0)
        unsafeCast p
      else (unsafeCast s : (Unit → String) × Nat).1 ())
    "" "ab"
@[implemented_by noiseImpl] opaque noise : String
end FoldPair
def foldpair1 (n : Nat) : Nat := n + 1
END
cat > FoldArray.lean <<'END'
namespace FoldArray
unsafe def noiseImpl : String :=
  String.Internal.foldl
    (fun s c => if c == 'a' then
        unsafeCast (#[fun (_ : Unit) => dbgTrace "FoldArray effect" fun _ => "x"] : Array (Unit → String))
      else (unsafeCast s : Array (Unit → String))[0]! ())
    "" "ab"
@[implemented_by noiseImpl] opaque noise : String
end FoldArray
def foldarray1 (n : Nat) : Nat := n + 1
END
cat > FoldChain.lean <<'END'
namespace FoldChain
unsafe def noiseImpl : String :=
  String.Internal.foldl
    (fun s c => if c == 'a' then
        unsafeCast (fun (_ : Unit) => (unsafeCast (fun (_ : Unit) =>
          dbgTrace "FoldChain effect" fun _ => "x") : String))
      else (unsafeCast s : Unit → String) ())
    "" "abc"
@[implemented_by noiseImpl] opaque noise : String
end FoldChain
def foldchain1 (n : Nat) : Nat := n + 1
END
cat > FoldOver.lean <<'END'
namespace FoldOver
-- (with a message that depends on its argument, or it would be a closed term, a constant of its own)
@[noinline] def effect (n : Nat) : String := dbgTrace (toString n) fun _ => "x"
@[noinline] unsafe def pick (s : String) (c : Char) : String :=
  if c == 'a' then unsafeCast effect else (unsafeCast s : Nat → String) 1
-- (a closure of one argument, that gives a closure: `foldl` gives it two)
unsafe def stepOver : String → Char → String := unsafeCast fun (s : String) => (unsafeCast (pick s) : Nat)
unsafe def noiseImpl : String := String.Internal.foldl stepOver "" "ab"
@[implemented_by noiseImpl] opaque noise : String
end FoldOver
def foldover1 (n : Nat) : Nat := n + 1
END
cat > FoldPartial.lean <<'END'
namespace FoldPartial
@[noinline] def effect2 (n : Nat) : String := dbgTrace (toString n) fun _ => "x"
@[noinline] def later (_ : Nat) : Nat → String := effect2
@[noinline] def step3 (s : String) (c : Char) (u : Unit) : Nat → String :=
  later (s.length + c.toNat + (if u == () then 0 else 1))
unsafe def noiseImpl : String :=
  (unsafeCast (String.Internal.foldl (unsafeCast step3) "" "a") : Unit → Nat → String) () 7
@[implemented_by noiseImpl] opaque noise : String
end FoldPartial
def foldpartial1 (n : Nat) : Nat := n + 1
END
cat > FoldThunk.lean <<'END'
namespace FoldThunk
unsafe def noiseImpl : String :=
  String.Internal.foldl
    (fun s c => if c == 'a' then
        unsafeCast (Thunk.pure (fun (_ : Unit) => dbgTrace "FoldThunk effect" fun _ => "x"))
      else (unsafeCast s : Thunk (Unit → String)).get ())
    "" "ab"
@[implemented_by noiseImpl] opaque noise : String
end FoldThunk
def foldthunk1 (n : Nat) : Nat := n + 1
END
cat > FoldInit.lean <<'END'
namespace FoldInit
structure Cfg where
  fn : String → String
  deriving Nonempty
initialize cfg : Cfg ← pure ⟨(· ++ "x")⟩
unsafe def noiseImpl : String := String.Internal.foldl (fun s _ => cfg.fn s) "" "ab"
@[implemented_by noiseImpl] opaque noise : String
end FoldInit
def foldinit1 (n : Nat) : Nat := n + 1
END

# An application of a value that nothing is known of may run anything, here what a constant holds.
cat > FoldBlind.lean <<'END'
namespace FoldBlind
def heldAct : Nat → IO Nat := fun n => do IO.println n; return n
@[noinline] unsafe def applyIt (b : Bool) (x : Nat) : Nat :=
  if b then (unsafeCast x : Nat → Nat) 1 else x
unsafe def blindImpl : Nat × (Nat → IO Nat) := (applyIt false 5, heldAct)
@[implemented_by blindImpl] opaque blind : Nat × (Nat → IO Nat)
end FoldBlind
def foldblind1 (n : Nat) : Nat := n + 1
END

# `profileit` takes no token, and reports what it measures if its options say so.
cat > FoldProfile.lean <<'END'
import Lean.Util.Profile
namespace FoldProfile
def noise : Nat := Lean.profileit "category" ({} : Lean.Options) (fun _ => 1)
end FoldProfile
def foldprofile1 (n : Nat) : Nat := n + 1
END
# C++ runs the closures of a `StateFactory`, an opaque type.
cat > FoldShare.lean <<'END'
namespace FoldShare
open ShareCommon
def builder : StateFactoryBuilder where
  Map α β _ _ := List (α × β)
  mkMap _ := []
  mapFind? m k := dbgTrace (toString (hash k)) fun _ => m.lookup k
  mapInsert m k v := (k, v) :: m
  Set α _ _ := List α
  mkSet _ := []
  setFind? s k := dbgTrace (toString (hash k)) fun _ => s.find? (· == k)
  setInsert s k := k :: s
def factory : StateFactory := StateFactory.mk builder
def shared : (List Nat × List Nat) × State factory :=
  State.shareCommon (σ := factory) (State.mk factory) ([1, 2], [1, 2])
end FoldShare
def foldshare1 (n : Nat) : Nat := n + 1
END
# An address is read through a closure, which is not a call of the package's.
cat > FoldPointer.lean <<'END'
namespace FoldPointer
@[noinline] def invoke (f : String → USize) (s : String) : USize := f s
def text : String := String.ofList (List.replicate 100 (Char.ofNat 97))
unsafe def addressImpl : USize := invoke ptrAddrUnsafe text
@[implemented_by addressImpl] opaque address : USize
initialize saved : USize ← pure address
end FoldPointer
def foldpointer1 (n : Nat) : Nat := n + 1
END
# (and one that is pure, which tells that the library is used at all)
cat > FoldKept.lean <<'END'
def foldkept1 (n : Nat) : Nat := n + (String.Internal.foldl (fun s c => s.push c) "" "ab").length
END
cat > UseFoldKept.lean <<'END'
import FoldKept
#eval foldkept1 1
END
FOLDS="FoldTrace FoldIndirect FoldPair FoldArray FoldChain FoldOver FoldPartial FoldThunk FoldInit FoldBlind FoldProfile FoldShare FoldPointer"
build $FOLDS FoldKept
native FoldTrace UseFoldKept.lean
check_out_contains "paperlean-timing native libs=1 modules=1"
same_as_plain UseFoldKept.lean
for m in $FOLDS; do
  cat > "Use$m.lean" <<END
import $m
#eval $(printf '%s' "$m" | tr 'A-Z' 'a-z')1 1
END
  native FoldTrace "Use$m.lean"
  check_out_contains "paperlean-timing native libs=0 modules=0"
  same_as_plain "Use$m.lean"
done

# Folds that do none of this keep their native code, with closures in their state.
cat > FoldPure.lean <<'END'
def total : String := String.Internal.foldl (fun s c => s.push c) "" "abc"
unsafe def viaStateImpl : String :=
  (unsafeCast (String.Internal.foldl
    (fun s c => unsafeCast (fun (t : String) => (unsafeCast s : String → String) (t.push c)))
    (unsafeCast (id : String → String)) "ab") : String → String) "x"
@[implemented_by viaStateImpl] opaque viaState : String
def pureAct : IO Nat := do IO.println "acting"; return total.length
def holdsPureAct : Nat × IO Nat := (viaState.length, pureAct)
def foldpure1 (n : Nat) : Nat := n + total.length + viaState.length
END
cat > UseFoldPure.lean <<'END'
import FoldPure
#eval foldpure1 1
#eval holdsPureAct.2
END
build FoldPure
native FoldPure UseFoldPure.lean
check_out_contains "paperlean-timing native libs=1 modules=1"
same_as_plain UseFoldPure.lean

# The primitives that take no world token, by their IR as the analysis tells, with a parameter that
# can hold a function, which an opaque type can: each runs it or is treated as if, is the Lean code
# behind an `@[extern]`, is impure anyway, or only holds it (`lean_mk_thunk`). A new one must go into
# `closureRunner` in `Lean.PaperLean.NativeLibs`, or here. None has an entry other than the name of a
# C function.
cat > Primitives.lean <<'END'
import Lean
import Lake
open Lean Meta
partial def holdsFn (seen : NameSet) (t : Expr) : MetaM Bool := do
  let t ← whnf t
  if t.isForall then return !(← inferType t).isProp
  let .const c _ := t.getAppFn | return false
  if c == ``Thunk || c == ``Task then return true
  if seen.contains c then return false
  let some (.inductInfo i) := (← getEnv).find? c | return false
  i.ctors.anyM fun ctor => do
    let some ci := (← getEnv).find? ctor | return false
    forallTelescopeReducing ci.type fun xs _ =>
      xs[i.numParams:].anyM fun x => do holdsFn (seen.insert c) (← inferType x)
#eval show MetaM Unit from do
  let env ← getEnv
  let mut out : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    unless isExtern env n do continue
    let some d := IR.findEnvDecl env n | continue
    if d.params.back?.any (·.ty matches .void) then continue
    let some entry := getExternEntryFor (getExternAttrData? env n |>.getD { entries := [] }) `c | continue
    let name := match entry with
      | .standard _ name => name
      | _ => s!"entry-of-{n}"
    let holds ← forallTelescopeReducing ci.type fun xs _ =>
      xs.anyM fun x => do
        let t ← whnf (← inferType x)
        let isOpaque := match t.getAppFn with
          | .const c _ => !(env.find? c matches some (.inductInfo _))
          | .fvar _ => false
          | _ => !t.isForall && !t.isSort
        return isOpaque || (← holdsFn {} t)
    if (holds || !(entry matches .standard ..)) && !out.contains name then out := out.push name
  for l in out.qsort (· < ·) do IO.println l
END
run_lean_primitives() { capture env LEAN_PATH="$LIB" lean Primitives.lean; }
run_lean_primitives
check_out_contains "lean_string_foldl"
check_out_contains "lean_kernel_whnf"
check_out_contains "lean_state_sharecommon"
for p in $(cat "$CAPTURED.out.produced"); do
  case "$p" in
    lean_thunk_*|lean_task_*|lean_find_*|lean_replace_*|lean_profileit|lean_paperlean_*|lean_idbg_*) ;;
    lean_string_any|lean_string_foldl|lean_string_nextwhile|lean_substring_all|lean_substring_takewhile) ;;
    lean_add_decl*|lean_elab_add_decl*|lean_kernel_*|lean_mk_cases_on|lean_state_sharecommon) ;;
    lean_get_ir_extra_const_names|lean_has_compile_error|lean_ir_export_entries|lean_is_reserved_name) ;;
    lean_dbg_*|lean_mk_thunk|lean_eval_const|lean_eval_check_meta) ;;
    # (what it takes comes from `IO`, and it reads a symbol)
    lean_dynlib_get) ;;
    *) fail "the primitive $p can hold a function and is not known to run it or not" ;;
  esac
done
# What C++ applies, as a type can hide a closure: a new file here must be looked at, for what its
# primitives do without a token.
sites=$(cd "$(dirname "$FILE")/../../src" &&
  grep -rlE 'lean_apply_[0-9nm]\b|[^_a-z]apply_[0-9nm]\b' --include=*.cpp . | sed 's|^\./||' |
  grep -v '^runtime/apply.cpp' | sort | tr '\n' ' ')
[ "$sites" = "kernel/for_each_fn.cpp kernel/replace_fn.cpp library/ir_interpreter.cpp library/time_task.cpp paperlean/env_recorder.cpp paperlean/fast_import.cpp paperlean/replace.cpp runtime/io.cpp runtime/object.cpp runtime/sharecommon.cpp runtime/uv/signal.cpp runtime/uv/tcp.cpp runtime/uv/timer.cpp runtime/uv/udp.cpp " ] ||
  fail "C++ that applies closures changed: $sites"

# Fields are told apart: a constant applies a pure closure of a structure that also holds `IO` code.
cat > Fields.lean <<'END'
structure Dict where
  pureF : Nat → Nat
  act : Nat → IO Nat
def dict : Dict := { pureF := (· + 1), act := fun n => do IO.println n; return n }
@[noinline] def useDict (d : Dict) : Nat := d.pureF 1
def viaField : Nat := useDict dict
def fields1 (n : Nat) : Nat := n + viaField
END
cat > UseFields.lean <<'END'
import Fields
#eval fields1 1
END
build Fields
native Fields UseFields.lean
check_out_contains "paperlean-timing native libs=1 modules=1"
same_as_plain UseFields.lean

# A module imported by others stops theirs, as they call its code.
cat > Importer.lean <<'END'
import Ref
def viaBump : IO Nat := bump
END
cat > UseImporter.lean <<'END'
import Importer
#eval viaBump
#eval viaBump
END
build Importer Ref
native Importer UseImporter.lean
check_out_contains "paperlean-timing native libs=0 modules=0"
same_as_plain UseImporter.lean

# Constants that are pure keep their native code: those that only hold code with effects without
# running it, too, and `[init]` declarations, which the interpreter runs as well.
cat > Pure.lean <<'END'
def table : Array Nat := (List.range 100).toArray.map (· * 2)
def act : IO Nat := do IO.println "acting"; return table[3]!.succ
def holdsAct : Nat × IO Nat := (1, act)
structure Tool where
  name : String
  run : Nat → IO Nat
def tool : Tool := { name := "tool", run := fun n => do IO.println n; return n }
def str : String := String.join (["a", "b"].map (· ++ "c"))
initialize cfg : IO.Ref Nat ← IO.mkRef 7
def readCfg : IO Nat := cfg.get
END
cat > UsePure.lean <<'END'
import Pure
#eval holdsAct.2
#eval tool.run 3
#eval str
#eval readCfg
END
build Pure
native Pure UsePure.lean
check_out_contains "paperlean-timing native libs=1 modules=1"
same_as_plain UsePure.lean

# A library with a symbol that nothing defines is not loaded, whenever the symbol would be called.
cat > Missing.lean <<'END'
@[noinline] def callee (n : Nat) : Nat := n + 41
@[noinline] def caller (n : Nat) : Nat := callee n
END
cat > UseMissing.lean <<'END'
import Missing
#eval caller 1
END
run env LEAN_PATH="$LIB" lean -o "$LIB/Missing.olean" -i "$LIB/Missing.ilean" -c "$TMP_DIR/Missing.c" Missing.lean
perl -pi -e 's/= l_callee\(/= l_callee_missing(/; s/^(#include <lean\/lean\.h>)$/$1\nlean_object* l_callee_missing(lean_object*);/' "$TMP_DIR/Missing.c"
grep -q "= l_callee_missing(" "$TMP_DIR/Missing.c" || fail "the test no longer changes the call"
# (clang rejects a call to an undeclared function)
grep -qx "lean_object\* l_callee_missing(lean_object\*);" "$TMP_DIR/Missing.c" ||
  fail "the test no longer declares the missing function"
run leanc -shared -DLEAN_EXPORTING -o "$TMP_DIR/libMissing.so" "$TMP_DIR/Missing.c"
run env LEAN_PATH="$LIB" lean --run "$TMP_DIR/native_helper.lean" manifest "$TMP_DIR/libMissing.paperlean" "$TMP_DIR/libMissing.so" "$TMP_DIR" Missing
rm -f "$TMP_DIR/all.paperlean"
capture lean --run "$TMP_DIR/pack.lean" "$TMP_DIR/all.paperlean" "$LIB"
native Missing UseMissing.lean
check_out_contains "warning: ignoring native library manifest"
check_out_contains "l_callee_missing"
check_out_contains "paperlean-timing native libs=0 modules=0"
check_out_contains "42"
