# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that `paperlean prepare` stops at an `@[export]` of a symbol that a dependency's library or Lean
# defines, which PaperLean does not support: it says so, naming the export and `lake build`, the package
# gets no native library, and the results are those without it. An `@[export]` of a package's own name
# is fine, as is one that implements an `@[extern]` of the same name in another of its modules.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN
ROOT="$(cd "$TMP_DIR" && pwd -P)"
mkdir -p "$ROOT/alpha" "$ROOT/beta" "$ROOT/root"
cd "$ROOT"
package() { # package <name> <lib> [dep]
  { printf 'name = "%s"\ndefaultTargets = ["%s"]\n' "$1" "$2"
    [ -z "${3:-}" ] || printf '[[require]]\nname = "%s"\npath = "../%s"\n' "$3" "$3"
    printf '[[lean_lib]]\nname = "%s"\n' "$2"; } > "$1/lakefile.toml"
}
package alpha A
cat > alpha/A.lean <<'END2'
@[noinline] def depFn (n : Nat) : Nat := n + 1
END2
package beta B alpha
cat > beta/B.lean <<'END2'
import A
@[export lp_alpha_depFn] def shadow (n : Nat) : Nat := n + 41
@[noinline] def useDep (n : Nat) : Nat := depFn n
END2
cat > root/lakefile.toml <<'END2'
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "beta"
path = "../beta"
[[lean_lib]]
name = "Root"
END2
cat > root/Root.lean <<'END2'
import B
END2
cat > root/Use.lean <<'END2'
import B
#eval depFn 1
#eval useDep 1
#eval shadow 1
END2
cat > root/UseProof.lean <<'END2'
import Lean
import B
open Lean Elab Tactic in
elab "rfl_if_shadowed" : tactic => do
  if useDep 1 != 42 then throwError "not shadowed"
  evalTactic (← `(tactic| rfl))
theorem t : 2 = 2 := by rfl_if_shadowed
#print axioms t
END2
cd root
# `same_as_plain <native modules>`: `Use.lean` gives what it gives without native code, with so many
same_as_plain() {
  capture lake lean Use.lean
  cp "$CAPTURED.out.produced" "$TMP_DIR/plain.out"
  capture env PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean Use.lean
  check_out_contains "paperlean-timing native libs=$1 modules=$1 "
  { grep -v "^paperlean-" "$CAPTURED.out.produced" || true; } | $DIFF -- "$TMP_DIR/plain.out" - ||
    fail "the native libraries change the output"
}

# the symbol of a dependency's module
run lake build Root
capture lake paperlean prepare -j 2
check_out_contains "PaperLean does not support \`@[export lp_alpha_depFn]\` (in B)"
check_out_contains "build this package with \`lake build\`"
check_out_contains "the native library of beta could not be built"
same_as_plain 1
for mode in "" PAPERLEAN_EXACT=1; do
  capture_exit 1 env $mode PAPERLEAN_ACCELERATE=1 lake lean UseProof.lean
  check_out_contains "not shadowed"
done
capture lake paperlean status
check_out_contains "native library of beta: not built ("

# a symbol of Lean
cat > ../beta/B.lean <<'END2'
import Lean
import A
open Lean
@[export lean_name_append_after] def shadow (_n : Name) (_s : String) : Name := `shadowed
@[noinline] def useDep (n : Nat) : Nat := depFn n
END2
sed -i.bak 's/^#eval shadow 1$/#eval shadow `a "b"/' Use.lean
run lake build Root
capture lake paperlean prepare -j 2
check_out_contains "PaperLean does not support \`@[export lean_name_append_after]\` (in B)"
same_as_plain 1

# a name of the package's own, also one that implements an `@[extern]` of another of its modules
cat > ../beta/B.lean <<'END2'
import A
import B.Decl
@[export paperlean_test_own] def shadow (n : Nat) : Nat := n + 41
@[noinline] def useDep (n : Nat) : Nat := depFn n
END2
mkdir ../beta/B
cat > ../beta/B/Decl.lean <<'END2'
@[extern "paperlean_test_impl"] opaque declared : Nat → Nat
END2
cat > ../beta/B/Impl.lean <<'END2'
@[export paperlean_test_impl] def implemented (n : Nat) : Nat := n + 2
END2
cat > ../beta/lakefile.toml <<'END2'
name = "beta"
defaultTargets = ["B"]
[[require]]
name = "alpha"
path = "../alpha"
[[lean_lib]]
name = "B"
globs = ["B", "B.+"]
END2
sed -i.bak 's/^#eval shadow `a "b"$/#eval shadow 1/' Use.lean
run lake build Root B.Impl
capture lake paperlean prepare -j 2
check_out_contains "Prepared"
! grep -q "PaperLean does not support" "$CAPTURED.out.produced" || fail "an export of the package's own name is refused"
# `A` and `B.Impl`: `B.Decl` declares an `@[extern]` function, and `B` imports it
capture lake paperlean status
check_out_contains "native library of beta: 3 modules"
same_as_plain 1
