# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that `paperlean prepare` decides by what really flows through primitives, end to end: a module
# whose constant makes a reference in a closure that `String.Internal.foldl` got back from its closure
# is interpreted, in the library of a package with a pure module that keeps its native code, and a proof
# that needs a counter to go up is rejected with and without `PAPERLEAN_EXACT`, as by the interpreter.
# Modules that are never imported together can define the same names: which code a name stands for
# cannot be told then, so that neither is decided by the other's code, in what a constant runs and in
# what an initializer does, whichever is read first, and what is evaluated now says nothing of the
# value that an initializer gives when the environment is another one. Nor does it for an initializer
# whose value can depend on whether registering an option failed, which earlier imports decide.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN
cp native_helper.lean "$TMP_DIR/"
ROOT="$(cd "$TMP_DIR" && pwd -P)"
mkdir -p "$ROOT/dep/Dep" "$ROOT/alpha" "$ROOT/beta" "$ROOT/inita" "$ROOT/initb" "$ROOT/root"
mkdir -p "$ROOT/caught"
cd "$ROOT"
cat > dep/lakefile.toml <<'END'
name = "dep"
defaultTargets = ["Dep"]
[[lean_lib]]
name = "Dep"
globs = ["Dep.+"]
END
cat > dep/Dep/FoldRef.lean <<'END'
unsafe def ctrImpl : IO.Ref Nat := unsafeCast <|
  String.Internal.foldl
    (fun s c => if c == 'a' then
        unsafeCast (fun (n : Nat) => (unsafeCast (unsafeBaseIO (IO.mkRef n)) : String))
      else (unsafeCast s : Nat → String) 0)
    "" "ab"
@[implemented_by ctrImpl] opaque ctr : IO.Ref Nat
def bump : IO Nat := do ctr.modify (· + 1); ctr.get
END
cat > dep/Dep/FoldPure.lean <<'END'
def total : String := String.Internal.foldl (fun s c => s.push c) "" "abc"
unsafe def viaStateImpl : String :=
  (unsafeCast (String.Internal.foldl
    (fun s c => unsafeCast (fun (t : String) => (unsafeCast s : String → String) (t.push c)))
    (unsafeCast (id : String → String)) "ab") : String → String) "x"
@[implemented_by viaStateImpl] opaque viaState : String
def pureAct : IO Nat := do IO.println "acting"; return total.length + viaState.length
END
package() { # package <name> <lib>
  printf 'name = "%s"\ndefaultTargets = ["%s"]\n[[lean_lib]]\nname = "%s"\n' "$1" "$2" "$2" > "$1/lakefile.toml"
}
# (whose code is the one that is read last, here `A`'s, so that `B` would pass for pure)
package alpha A
cat > alpha/A.lean <<'END'
def same : Nat := 5
def alpha1 (n : Nat) : Nat := n + same
END
package beta B
cat > beta/B.lean <<'END'
def same : Nat := dbgTrace "B.same evaluated" fun _ => 5
def beta1 (n : Nat) : Nat := n + 1
END
# (a helper of the same name, and only `InitB`'s reads the environment)
package inita InitA
cat > inita/InitA.lean <<'END'
@[noinline] def sharedHelper (_ : Unit) : IO Nat := pure 0
END
package initb InitB
cat > initb/InitB.lean <<'END'
@[noinline] def sharedHelper (_ : Unit) : IO Nat := do
  let v ← IO.getEnv "PREPARE_CALLBACKS_INIT"
  return if v.isSome then 1 else 0
initialize bValue : Nat ← sharedHelper ()
def unusedValue : Nat := if bValue == 0 then 7 else panic! "the value depends on the environment"
def keep (n : Nat) : Nat := n + 1
END
# Each with an option of its own, so that none finds the option of another while `prepare` evaluates
# them: what `registerOption` gives is `ok` there, and `error` after `Before`.
regOption() { # regOption <option>: an `IO Unit` that registers the option
  printf 'registerOption `%s { name := `%s, defValue := .ofBool false, descr := "x" }' "$1" "$1"
}
caught() { # caught <module>: the standard input in a namespace of that name, with a header
  { printf 'import Lean.Data.Options\nopen Lean\nnamespace %s\n' "$1"
    printf 'abbrev Out (a : Type) := EST.Out IO.Error IO.RealWorld a\n'; cat; printf 'end %s\n' "$1"; } > "caught/$1.lean"
}
# the error branch gives what it was given
caught CatchFallback <<END
@[noinline] def recover (fallback : Out Nat) (w : Void IO.RealWorld) : Out Nat :=
  match $(regOption review.fallback) w with
  | .ok _ w' => .ok 0 w'
  | .error _ _ => fallback
initialize value : Nat ← fun w => recover (.ok 100 w) w
def unused : Nat := if value == 0 then 7 else panic! "CatchFallback"
END
# ... through a join point
caught CatchJoin <<END
@[noinline] def recover (fallback : Out Nat) (b : Bool) (w : Void IO.RealWorld) : Out Nat :=
  let r : Out Nat := match $(regOption review.join) w with
    | .ok _ w' => .ok 0 w'
    | .error _ _ => if b then fallback else fallback
  match r with
  | .ok v w' => .ok (v + 0) w'
  | e => e
initialize value : Nat ← fun w => recover (.ok 100 w) true w
def unused : Nat := if value == 0 then 7 else panic! "CatchJoin"
END
# ordinary \`try\`
caught CatchTry <<END
initialize value : Nat ← do
  try $(regOption review.try); return 0
  catch _ => return 100
def unused : Nat := if value == 0 then 7 else panic! "CatchTry"
END
# no \`case\` in the initializer: what it did goes into its value, and the constant looks
caught CatchValue <<END
@[noinline] def wrap (r : Out Unit) : Option (Out Unit) := some r
initialize value : Option (Out Unit) ← fun w => .ok (wrap ($(regOption review.value) w)) w
def unused : Nat := match value with
  | some (.error _ _) => panic! "CatchValue"
  | _ => 7
END
# a helper looks
caught CatchHelper <<END
@[noinline] def isGood (r : Out Unit) (w : Void IO.RealWorld) : Out Nat :=
  match r with
  | .ok _ _ => .ok 0 w
  | .error _ _ => .ok 100 w
initialize value : Nat ← fun w => isGood ($(regOption review.helper) w) w
def unused : Nat := if value == 0 then 7 else panic! "CatchHelper"
END
# \`unsafeCast\` gives the \`case\` other constructors, with their tags the other way around
caught CatchCast <<END
unsafe def pickImpl (w : Void IO.RealWorld) : Out Nat :=
  match (unsafeCast ($(regOption review.cast) w) : Except IO.Error Unit) with
  | .ok _ => .ok 100 w
  | .error _ => .ok 0 w
@[implemented_by pickImpl] def pick (w : Void IO.RealWorld) : Out Nat := .ok 0 w
initialize value : Nat ← fun w => pick w
def unused : Nat := if value == 0 then 7 else panic! "CatchCast"
END
# a function without a token, which does not count as one that can fail
caught CatchTokenless <<END
unsafe def quietImpl (n : Nat) : Option Nat :=
  unsafeCast (match $(regOption review.tokenless) (unsafeCast n) with
    | .ok _ w' => (.ok () w' : Out Unit)
    | .error e w' => (.error e w' : Out Unit))
@[implemented_by quietImpl] opaque quiet (n : Nat) : Option Nat
@[noinline] def tell (n : Nat) (w : Void IO.RealWorld) : Out Nat :=
  match quiet n with
  | none => .ok 0 w
  | some _ => .ok 100 w
initialize value : Nat ← tell 1
def unused : Nat := if value == 0 then 7 else panic! "CatchTokenless"
END
# what stays: \`register_option\`, also through a function that passes the error on, and the error
caught CatchPure <<END
register_option review.pure : Nat := { defValue := 3, descr := "x" }
def viaHelper : IO (Lean.Option Bool) := do
  let o ← Lean.Option.register \`review.pure2 { defValue := true, descr := "x" }
  return o
initialize pure2 : Lean.Option Bool ← viaHelper
def checked : Nat := if review.pure.defValue == 3 && pure2.defValue then 7 else panic! "CatchPure"
def pureKeep (n : Nat) : Nat := n + checked
END
CATCHES="CatchFallback CatchJoin CatchTry CatchValue CatchHelper CatchCast CatchTokenless"
{ printf 'name = "caught"\n[[lean_lib]]\nname = "Caught"\nroots = [%s"CatchPure"]\n' \
    "$(for m in $CATCHES; do printf '"%s", ' "$m"; done)"; } > caught/lakefile.toml
rootConfig() { # rootConfig <package>...: the root package, with its requirements in that order
  { printf 'name = "root"\ndefaultTargets = ["Root"]\n'
    for p in "$@"; do printf '[[require]]\nname = "%s"\npath = "../%s"\n' "$p" "$p"; done
    printf '[[lean_lib]]\nname = "Root"\n[[lean_lib]]\nname = "Before"\n[[lean_lib]]\nname = "BeforePure"\n'; } > root/lakefile.toml
}
rootConfig dep alpha beta inita initb caught
cat > root/Before.lean <<END
import Lean.Data.Options
open Lean
$(for o in fallback join try value helper cast tokenless; do printf 'initialize %s\n' "$(regOption review.$o)"; done)
END
cat > root/BeforePure.lean <<END
import Lean.Data.Options
open Lean
initialize $(regOption review.pure)
END
cat > root/Root.lean <<'END'
import Dep.FoldRef
import Dep.FoldPure
END
printf 'import %s\n' $CATCHES CatchPure >> root/Root.lean
cat > root/Use.lean <<'END'
import Dep.FoldRef
#eval bump
#eval bump
END
cat > root/UsePure.lean <<'END'
import Dep.FoldPure
#eval pureAct
END
cat > root/UseA.lean <<'END'
import A
#eval alpha1 1
END
cat > root/UseB.lean <<'END'
import B
#eval beta1 1
END
cat > root/UseInitB.lean <<'END'
import InitB
#eval keep 1
END
cat > root/Proof.lean <<'END'
import Lean
import Dep.FoldRef
#eval bump
open Lean Elab Tactic in
elab "rfl_after_counter" : tactic => do
  let n ← bump
  if n < 2 then throwError "not warmed up"
  evalTactic (← `(tactic| rfl))
theorem t : 2 = 2 := by rfl_after_counter
#print axioms t
END
cd root
run lake build Root A B InitA InitB Before BeforePure
capture lake paperlean prepare -j 2
check_out_contains "Prepared"
check_out_contains "dep: 2 modules, 1 interpreted"
check_out_contains "e.g. Dep.FoldRef: "
check_out_contains "alpha: 1 modules, 1 interpreted"
check_out_contains "beta: 1 modules, 1 interpreted"

plain_vs_native() { # plain_vs_native <file> <what native output has>
  capture lake lean "$1"
  cp "$CAPTURED.out.produced" "$TMP_DIR/plain.out"
  capture env LEAN_BACKTRACE=0 PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean "$1"
  check_out_contains "$2"
  { grep -v "^paperlean-" "$CAPTURED.out.produced" || true; } | $DIFF -- "$TMP_DIR/plain.out" - ||
    fail "the native libraries change the output of $1"
}
plain_vs_native Use.lean "paperlean-timing native libs=0 modules=0 "
[ "$(cat "$TMP_DIR/plain.out")" = "$(printf '1\n1')" ] || fail "the counter is shared by the runs"
plain_vs_native UsePure.lean "paperlean-timing native libs=1 modules=1 "
plain_vs_native UseA.lean "paperlean-timing native libs=0 modules=0 "
plain_vs_native UseB.lean "paperlean-timing native libs=0 modules=0 "
for mode in "" PAPERLEAN_EXACT=1; do
  capture_exit 1 env $mode PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean Proof.lean
  check_out_contains "not warmed up"
  check_out_contains "paperlean-timing native libs=0 modules=0 "
  if grep -q "does not depend on any axioms" "$CAPTURED.out.produced"; then
    fail "Proof.lean is accepted"
  fi
done

# What an initializer runs, in both orders of the packages and of the modules. The analysis of
# `InitB` must not depend on `InitA`, and the proof of that is the environment at import: `prepare` did
# not have the variable, so that `unusedValue` evaluated without a panic.
for order in "inita initb" "initb inita"; do
  cd "$ROOT"
  rootConfig dep alpha beta caught $order
  cd root
  run lake build Root A B InitA InitB Before BeforePure
  capture lake paperlean prepare -j 2
  check_out_contains "Prepared"
  check_out_contains "initb: 1 modules, 1 interpreted"
  check_out_contains "e.g. InitB: "
  export PREPARE_CALLBACKS_INIT=1
  capture lake lean UseInitB.lean
  cp "$CAPTURED.out.produced" "$TMP_DIR/plain.out"
  [ "$(cat "$TMP_DIR/plain.out")" = "2" ] || fail "the plain output of UseInitB.lean is not 2"
  for mode in "" PAPERLEAN_EXACT=1; do
    capture env $mode LEAN_BACKTRACE=0 PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean UseInitB.lean
    check_out_contains "paperlean-timing native libs=0 modules=0 "
    { grep -v "^paperlean-" "$CAPTURED.out.produced" || true; } | $DIFF -- "$TMP_DIR/plain.out" - ||
      fail "the native libraries change the output of UseInitB.lean ($order, $mode)"
  done
  # (a module that has nothing to do with it keeps its native code)
  plain_vs_native UsePure.lean "paperlean-timing native libs=1 modules=1 "
  unset PREPARE_CALLBACKS_INIT
done
capture lake env lean --run "$ROOT/native_helper.lean" check InitB InitA
check_out_contains "impure InitB.olean"
check_out_contains "bad=1"
capture lake env lean --run "$ROOT/native_helper.lean" check InitA InitB
check_out_contains "impure InitB.olean"
check_out_contains "bad=1"

# A module that cannot be read has not been decided, whatever looks at the verdicts.
capture lake env lean --run "$ROOT/native_helper.lean" unread
check_out_contains "bad=1"

# What comes of registering an option. Each module is impure by itself and in the same way in `prepare`,
# and after `Before`, where registering fails, an unused constant does not panic at import.
cd "$ROOT"
rootConfig dep alpha beta inita initb caught
cd root
run lake build Root A B InitA InitB Before BeforePure
capture lake paperlean prepare -j 2
check_out_contains "caught: 8 modules, 7 interpreted"
for m in $CATCHES; do
  cat > "Use$m.lean" <<END
import Before
import $m
#eval 1 + 1
END
  capture lake env lean --run "$ROOT/native_helper.lean" check "$m"
  check_out_contains "impure $m.olean"
  check_out_contains "bad=1"
  capture lake lean "Use$m.lean"
  cp "$CAPTURED.out.produced" "$TMP_DIR/plain.out"
  [ "$(cat "$TMP_DIR/plain.out")" = "2" ] || fail "the plain output of Use$m.lean is not 2"
  for mode in "" PAPERLEAN_EXACT=1; do
    capture env $mode LEAN_BACKTRACE=0 PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean "Use$m.lean"
    check_out_contains "paperlean-timing native libs=0 modules=0 "
    { grep -v "^paperlean-" "$CAPTURED.out.produced" || true; } | $DIFF -- "$TMP_DIR/plain.out" - ||
      fail "the native libraries change the output of Use$m.lean ($mode)"
  done
done
capture lake env lean --run "$ROOT/native_helper.lean" check CatchPure
check_out_contains "bad=0"
cat > UseCatchPure.lean <<'END'
import CatchPure
#eval CatchPure.pureKeep 1
END
plain_vs_native UseCatchPure.lean "paperlean-timing native libs=1 modules=1 "
# An error that is not caught ends the import, whatever the code runs in, and the message is the same.
cat > UseDuplicate.lean <<'END'
import BeforePure
import CatchPure
#eval CatchPure.pureKeep 1
END
capture_exit 1 lake lean UseDuplicate.lean
cp "$CAPTURED.out.produced" "$TMP_DIR/plain.out"
check_out_contains "Option already exists"
capture_exit 1 env LEAN_BACKTRACE=0 PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean UseDuplicate.lean
check_out_contains "paperlean-timing native libs=1 modules=1 "
{ grep -v "^paperlean-" "$CAPTURED.out.produced" || true; } | $DIFF -- "$TMP_DIR/plain.out" - ||
  fail "the native libraries change the output of UseDuplicate.lean"
