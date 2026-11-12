# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that what `paperlean prepare` finds out about a module holds for the files that it looked at,
# and for no others, whatever happens to them while it runs: `lake build` can replace a module's files
# after the analysis and before the module is compiled, and the files that are compiled then are not
# known to be pure. A `paperlean prepare <package>` that writes a new pack afterwards, and keeps the
# library, must not bring such a module into use. Modules that did not change keep their native code.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN LEAN_CC
cp native_helper.lean "$TMP_DIR/"
ROOT="$(cd "$TMP_DIR" && pwd -P)"
mkdir -p "$ROOT/dep/Dep" "$ROOT/other" "$ROOT/root"
cd "$ROOT"
cat > dep/lakefile.toml <<'END'
name = "dep"
defaultTargets = ["Dep"]
[[lean_lib]]
name = "Dep"
globs = ["Dep.+"]
END
cat > dep/Dep/A.lean <<'END'
def a (n : Nat) : Nat := n + 1
END
cat > dep/Dep/Z.lean <<'END'
def z (n : Nat) : Nat := n + 1
END
cat > "$ROOT/impureZ.lean" <<'END'
unsafe def ctrImpl : IO.Ref Nat := unsafeBaseIO (IO.mkRef 0)
@[implemented_by ctrImpl] opaque ctr : IO.Ref Nat
def bump : IO Nat := do ctr.modify (· + 1); ctr.get
def z (n : Nat) : Nat := n + 1
END
# What a module's constant runs can be in an import that changes while the module does not: the body
# of `priv` is not part of what `Dep.User` is built from. No constant of `Dep.Priv` shows what it does.
cat > dep/Dep/Priv.lean <<'END'
module
public def priv (n : Nat) : Nat := n + 1
END
cat > "$ROOT/impurePriv.lean" <<'END'
module
public def priv (n : Nat) : Nat := if n == 1 then panic! "Dep.Priv" else n + 1
END
cat > dep/Dep/User.lean <<'END'
module
public import Dep.Priv
public def usesPriv : Nat := priv 1
END
# A module with a constant to evaluate, whose file a module's initializer changes when the process that
# evaluates constants imports it: after it was read, before there is a verdict.
cat > dep/Dep/Victim.lean <<'END'
def victim : Nat := (List.range 10).length
END
cat > dep/Dep/Touch.lean <<'END'
initialize do
  if let some f ← IO.getEnv "PREPARE_RACE_TOUCH" then
    unless ← System.FilePath.pathExists (f ++ ".done") do
      IO.FS.writeFile (f ++ ".done") ""
      discard <| IO.Process.run { cmd := "touch", args := #[f] }
END
cat > other/lakefile.toml <<'END'
name = "other"
defaultTargets = ["Other"]
[[lean_lib]]
name = "Other"
END
cat > other/Other.lean <<'END'
def unrelated (n : Nat) : Nat := n + 3
END
cat > root/lakefile.toml <<'END'
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "dep"
path = "../dep"
[[require]]
name = "other"
path = "../other"
[[lean_lib]]
name = "Root"
END
cat > root/Root.lean <<'END'
import Dep.A
import Dep.Z
import Dep.User
import Dep.Victim
import Dep.Touch
import Other
END
cat > root/Use.lean <<'END'
import Dep.Z
#eval bump
#eval bump
END
cat > root/Proof.lean <<'END'
import Lean
import Dep.Z
open Lean Elab Tactic
#eval bump
elab "after_warmup" : tactic => do
  let n ← bump
  if n < 2 then throwError "not warmed up"
  evalTactic (← `(tactic| rfl))
theorem checkedAfterWarmup : 2 = 2 := by after_warmup
#print axioms checkedAfterWarmup
END
cat > root/UseA.lean <<'END'
import Dep.A
#eval a 1
END
cat > root/UseOther.lean <<'END'
import Other
#eval unrelated 1
END
cat > root/UseUser.lean <<'END'
import Dep.User
#eval 1 + 1
END
# Pause the actual default C driver after verification, without replacing it or its flags.
# (a glob, not `compgen -G`: bash built without programmable completion, as Nix's, has no `compgen`)
has_blocked() { local f; for f in "$ROOT"/blocked-*; do [ -e "$f" ] && return 0; done; return 1; }
paused() { # paused <log> <command>...: `prepare` runs in the background until the analysis is done
  rm -f "$ROOT"/blocked-* "$ROOT/release" "$ROOT/eval.events" "$1"
  # (the compiler runs, as no compiled object is in the cache)
  rm -rf "$PAPERLEAN_CACHE_DIR"/prepared/*/objects
  local log="$1"
  shift
  PAPERLEAN_NATIVE_COMPILER_GATE="$ROOT" PAPERLEAN_NATIVE_COMPILER_GATE_INPUT=/Dep/A.c \
    PAPERLEAN_EVAL_EVENTS="$ROOT/eval.events" PAPERLEAN_UNIT_BYTES=0 lake paperlean prepare -j 1 "$@" > "$log" 2>&1 &
  PREPARE=$!
  local n
  for ((n = 0; n < 2400; n++)); do
    has_blocked && grep -q '^done$' "$ROOT/eval.events" 2>/dev/null && return 0
    sleep 0.1
  done
  fail "prepare did not get to the point of the test"
}
same_as_plain() { # same_as_plain <file> <what the accelerated output has>
  capture lake lean "$1"
  cp "$CAPTURED.out.produced" "$TMP_DIR/plain.out"
  for mode in "" PAPERLEAN_EXACT=1; do
    capture env $mode LEAN_BACKTRACE=0 PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean "$1"
    check_out_contains "$2"
    { grep -v "^paperlean-" "$CAPTURED.out.produced" || true; } | $DIFF -- "$TMP_DIR/plain.out" - ||
      fail "the native libraries change the output of $1 ($mode)"
  done
}

cd root
run lake build
# The files of two modules are replaced after the analysis, by an ordinary `lake build`, one with
# an impure module, the other with an impure function in a module whose importer is not built again.
paused "$ROOT/prepare1.log"
cp "$ROOT/impureZ.lean" ../dep/Dep/Z.lean
cp "$ROOT/impurePriv.lean" ../dep/Dep/Priv.lean
touch "$ROOT/before-build"
(cd ../dep && run lake build)
if [ ../dep/.lake/build/lib/lean/Dep/User.olean -nt "$ROOT/before-build" ]; then
  fail "Dep.User was built again, and does not test what it should"
fi
touch "$ROOT/release"
wait "$PREPARE" || fail "prepare failed"
cat "$ROOT/prepare1.log"
grep -q "interpreted" "$ROOT/prepare1.log" || fail "the changed modules are not interpreted"
grep -Eq '^  e\.g\. Dep\.Z: (\.c has no prepared content hash|\.c bytes do not match the prepared content hash|its files changed after they were analysed)$' "$ROOT/prepare1.log" ||
  fail "Dep.Z is not reported as changed"
grep -Eq '^  e\.g\. Dep\.Priv: (\.c has no prepared content hash|\.c bytes do not match the prepared content hash|its files changed after they were analysed)$' "$ROOT/prepare1.log" ||
  fail "Dep.Priv is not reported as changed"
# (`Dep.User` is as it was, and stays out through its import)
if grep -q "e.g. Dep.User: its files" "$ROOT/prepare1.log"; then
  fail "Dep.User is reported as changed, though its files did not change"
fi

# A new pack of the files as they are now, with the library of `dep` kept.
capture lake paperlean prepare other -j 1
check_out_contains "Prepared"
same_as_plain Use.lean "paperlean-timing native libs=0 modules=0 "
[ "$(cat "$TMP_DIR/plain.out")" = "$(printf '1\n1')" ] || fail "the counter is shared by the runs"
capture_exit 1 lake lean Proof.lean
check_out_contains "not warmed up"
for mode in "" PAPERLEAN_EXACT=1; do
  capture_exit 1 env $mode LEAN_BACKTRACE=0 PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean Proof.lean
  check_out_contains "not warmed up"
  check_out_contains "paperlean-timing native libs=0 modules=0 "
  if grep -q "does not depend on any axioms" "$CAPTURED.out.produced"; then
    fail "Proof.lean is accepted"
  fi
done
same_as_plain UseUser.lean "paperlean-timing native libs=0 modules=0 "
# (modules that nothing happened to, in the same library and in another one)
same_as_plain UseA.lean "paperlean-timing native libs=1 modules=1 "
same_as_plain UseOther.lean "paperlean-timing native libs=1 modules=1 "

# A file that changes after it was read, while its module's constants are evaluated: the process tells.
# (`Dep.Victim` is compiled after that, from the file as it is then, whose trace still matches.)
VICTIM="$ROOT/dep/.lake/build/lib/lean/Dep/Victim.olean"
PREPARE_RACE_TOUCH="$VICTIM" paused "$ROOT/prepare2.log"
touch "$ROOT/release"
wait "$PREPARE" || fail "prepare failed"
cat "$ROOT/prepare2.log"
grep -Eq '^  e\.g\. Dep\.Victim: (\.olean has no prepared content hash|its files changed while it was analysed)$' "$ROOT/prepare2.log" ||
  fail "Dep.Victim is not reported as changed while it was analysed"
same_as_plain UseA.lean "paperlean-timing native libs=1 modules=1 "

# ... also in the analysis itself, whatever looks at its verdicts.
rm -f "$VICTIM.done"
capture env PREPARE_RACE_TOUCH="$VICTIM" lake env lean --run "$ROOT/native_helper.lean" check Dep.Victim Dep.Touch
check_out_contains "impure Victim.olean: its files changed while it was analysed"
check_out_contains "bad=1"
capture lake env lean --run "$ROOT/native_helper.lean" check Dep.Victim Dep.Touch
check_out_contains "bad=0"
