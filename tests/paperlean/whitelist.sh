# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests the whitelist of elaborators that a recording may run (`Lean.PaperLean.Whitelist`), with Mathlib's
# `Type*`, whose module is copied here with the same code under the same name: its variables are reused,
# also in another namespace, compiled by PaperLean or by official Lean (byte-identical outputs to a run
# that reuses nothing, and no difference found by the oracle). A changed version under the same name, here
# in a helper that the elaborator calls, is not trusted, and neither is one of the current file: each is
# elaborated as Lean does, and the statistics say why. The hash of the code does not depend on what else
# is imported. It needs official Lean, at `$OFFICIAL_LEAN_TOOLCHAIN` or elan's, and fails without it.

OFFICIAL=${OFFICIAL_LEAN_TOOLCHAIN:-$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3}
[ -x "$OFFICIAL/bin/lean" ] ||
  fail "official Lean 4.35.0-rc3 is not at $OFFICIAL (set OFFICIAL_LEAN_TOOLCHAIN to where it is)"
cd "$TMP_DIR"
mkdir -p vetted/Mathlib/Tactic official/Mathlib/Tactic changed/Mathlib/Tactic
# (Mathlib's file but for its import)
cat > vetted/Mathlib/Tactic/TypeStar.lean <<'EOF'
module

public meta import Lean.Elab.ElabRules

public meta section

namespace Lean.Elab.Term

partial def mkFreshLevelName (usedLevelNames : List Name) (namePrefix : Name := `u) : Name :=
  go 1
where
  go n : Name :=
    let u := namePrefix.appendIndexAfter n
    if usedLevelNames.contains u then go (n+1) else u

def mkFreshLevelParam (namePrefix : Name := `u)
    (insert : List Name → Name → List Name := (·.cons)) : TermElabM Level := do
  let levelNames ← getLevelNames
  let u := mkFreshLevelName levelNames namePrefix
  setLevelNames <| insert levelNames u
  return mkLevelParam u

elab "Sort*" : term => return .sort <| ← mkFreshLevelParam

elab "Type*" : term => return .sort <| .succ <| ← mkFreshLevelParam

end Lean.Elab.Term
EOF
cp vetted/Mathlib/Tactic/TypeStar.lean official/Mathlib/Tactic/
sed 's/^  go 1$/  go 2/' vetted/Mathlib/Tactic/TypeStar.lean > changed/Mathlib/Tactic/TypeStar.lean
(cd vetted && lean --root=. -o Mathlib/Tactic/TypeStar.olean Mathlib/Tactic/TypeStar.lean &&
  cd ../changed && lean --root=. -o Mathlib/Tactic/TypeStar.olean Mathlib/Tactic/TypeStar.lean &&
  cd ../official && "$OFFICIAL/bin/lean" --root=. -o Mathlib/Tactic/TypeStar.olean Mathlib/Tactic/TypeStar.lean) \
  > build.out 2>&1 || fail "the copies of Type* failed: $(cat build.out)"

cat > Main.lean <<'EOF'
import Mathlib.Tactic.TypeStar
variable (α : Type*) (a : α)
theorem t1 : a = a := rfl
theorem t2 : a = a := rfl
namespace A
theorem t3 : a = a := rfl
end A
#check @A.t3
EOF
# <directory of the module>
reuse() {
  LEAN_PATH=$1 PAPERLEAN_REUSE=1 PAPERLEAN_REUSE_STATS=$1.stats lean -o $1.reuse.olean Main.lean > $1.reuse.out 2>&1 ||
    fail "Main.lean with $1: $(cat $1.reuse.out)"
  LEAN_PATH=$1 PAPERLEAN_EXACT=1 lean -o $1.exact.olean Main.lean > $1.exact.out 2>&1 ||
    fail "Main.lean with $1: $(cat $1.exact.out)"
  cmp -s $1.reuse.olean $1.exact.olean || fail "Main.lean with $1: the .olean differs from a run that reuses nothing"
  $DIFF -- $1.exact.out $1.reuse.out || fail "Main.lean with $1: the output differs from a run that reuses nothing"
}
for d in vetted official; do
  reuse $d
  awk -F '\t' '$6 == 2' $d.stats | grep -q . || fail "the variables of Type*, compiled in $d, were not reused: $(cat $d.stats)"
  LEAN_PATH=$d PAPERLEAN_REUSE=1 PAPERLEAN_REUSE_ORACLE=1 lean Main.lean > $d.oracle.out 2>&1 ||
    fail "Main.lean with $d: $(cat $d.oracle.out)"
  $DIFF -- $d.exact.out $d.oracle.out || fail "Main.lean with $d: the output with the oracle differs"
done
grep -q "A.t3 : ∀ (α : Type u_[0-9]" vetted.exact.out || fail "Main.lean does not test what it should: $(cat vetted.exact.out)"

# another version under the same name
reuse changed
awk -F '\t' '$6 == 0' changed.stats | grep -q . || fail "a changed Type* was reused: $(cat changed.stats)"
grep -q "whose code is not the code vetted=" changed.stats || fail "the statistics do not say why: $(cat changed.stats)"

# the same name in the file itself
mkdir -p local/Mathlib/Tactic
cat vetted/Mathlib/Tactic/TypeStar.lean > local/Mathlib/Tactic/TypeStar.lean
cat >> local/Mathlib/Tactic/TypeStar.lean <<'EOF'
variable (α : Type*) (a : α)
public theorem t1 : a = a := rfl
public theorem t2 : a = a := rfl
EOF
(cd local && PAPERLEAN_REUSE=1 PAPERLEAN_REUSE_STATS=../local.stats lean --root=. Mathlib/Tactic/TypeStar.lean) \
  > local.out 2>&1 || fail "the file with Type*: $(cat local.out)"
awk -F '\t' '$6 == 0' local.stats | grep -q . || fail "an elaborator of the file was reused: $(cat local.stats)"
grep -q "whose code is not the code vetted=" local.stats || fail "the statistics do not say why: $(cat local.stats)"

# the hash of the code does not depend on what else is imported
cat > Hash.lean <<'EOF'
import Mathlib.Tactic.TypeStar
import Lean
open Lean
#eval do
  let h := PaperLean.Whitelist.codeHash (← getEnv) ``Lean.Elab.Term.«_aux_Mathlib_Tactic_TypeStar___elabRules_Lean_Elab_Term_termType*_1»
  logInfo m!"on the list: {PaperLean.Whitelist.entries.any (·.hash == h)}"
EOF
LEAN_PATH=vetted lean Hash.lean > hash.out 2>&1 || fail "Hash.lean: $(cat hash.out)"
grep -q "on the list: true" hash.out || fail "the hash of Type* is not on the list: $(cat hash.out)"
