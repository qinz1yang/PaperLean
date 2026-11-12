# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that the whitelist's cache of vetted code (`Lean.PaperLean.Whitelist.isVetted`) is keyed by
# the imported code, not only by the entry's declaration name: two frontends of one process import
# the same module name (`Mathlib.Tactic.TypeStar`) from two search paths, one a copy of the vetted
# `Type*` (`go 1`) and one a changed copy (`go 2`, same declaration names).  `noteEntry` for the
# vetted environment first, then for the changed one: the changed environment's code hash is not the
# stored hash, so the recording must become unusable with "whose code is not the code vetted".  On
# 0.2.3 the changed environment is served the vetted environment's cached `true` and no reason is
# given.  The driver also checks that both environments agree on the module index (so a cache keyed
# by the module index alone would still fail this test) and prints what a cache keyed by the
# environment header gives (the fixed model).  Needs no official Lean.

cd "$TMP_DIR"
mkdir -p vetted/Mathlib/Tactic changed/Mathlib/Tactic
cat > vetted/Mathlib/Tactic/TypeStar.lean <<'SRC'
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
SRC
sed 's/^  go 1$/  go 2/' vetted/Mathlib/Tactic/TypeStar.lean > changed/Mathlib/Tactic/TypeStar.lean
(cd vetted && lean --root=. -o Mathlib/Tactic/TypeStar.olean Mathlib/Tactic/TypeStar.lean) \
  > build-vetted.out 2>&1 || fail "the vetted copy of Type* failed: $(cat build-vetted.out)"
(cd changed && lean --root=. -o Mathlib/Tactic/TypeStar.olean Mathlib/Tactic/TypeStar.lean) \
  > build-changed.out 2>&1 || fail "the changed copy of Type* failed: $(cat build-changed.out)"
cp "$(dirname "$FILE")/WhitelistCacheTest.lean" .
capture_exit 0 lean --run WhitelistCacheTest.lean
out="$CAPTURED.out.produced"
# (the changed copy is another code, under the same module name and module index)
grep -q "^vetted env: module (some [0-9]*), hash [0-9]*$" "$out" || fail "the vetted copy: $(cat "$out")"
grep -q "^changed env: module (some [0-9]*), hash [0-9]*$" "$out" || fail "the changed copy: $(cat "$out")"
[ "$(grep -o "whose code is not the code vetted" "$out" | wc -l | tr -d ' ')" = 2 ] ||
  fail "the changed code of a vetted entry was trusted (the cache serves another environment's answer): $(cat "$out")"
grep -q "reasons: vetted '', changed '.*whose code is not the code vetted', vetted '', changed '.*whose code is not the code vetted'" "$out" ||
  fail "the reasons are not those of the patched check: $(cat "$out")"
grep -q "^fixed model: vetted true, changed false, vetted true, changed false$" "$out" ||
  fail "a cache keyed by the environment header does not tell the two environments apart: $(cat "$out")"
