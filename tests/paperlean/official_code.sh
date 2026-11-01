# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that files that see the specializations of imported modules, non-module files and `module`s
# with `import all`, compile to official Lean 4.35.0-rc3's code, also with reuse:
# - the compiler's cache of specializations (`official_code.lean`) is official Lean's, with no
#   specialization of PaperLean's own code, but for the keys of the upstream functions listed, whose
#   bodies carry PaperLean's hooks: their specializations keep their names under other keys;
# - the C code of such files, with specializations that the cache has, is official Lean's byte for byte.
# It needs official Lean, at `$OFFICIAL_LEAN_TOOLCHAIN` or elan's, and fails without it.
OFFICIAL=${OFFICIAL_LEAN_TOOLCHAIN:-$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3}
[ -x "$OFFICIAL/bin/lean" ] ||
  fail "official Lean 4.35.0-rc3 is not at $OFFICIAL (set OFFICIAL_LEAN_TOOLCHAIN to where it is)"

cp official_code.lean "$TMP_DIR/"
cd "$TMP_DIR"
export LC_ALL=C

"$OFFICIAL/bin/lean" --run official_code.lean "$OFFICIAL/lib/lean" spec.official ||
  fail "official Lean cannot read its cache of specializations"
LEAN_PATH= lean --run official_code.lean "$BUILD_DIR/lib/lean" spec.paperlean ||
  fail "PaperLean cannot read its cache of specializations"
sort -u spec.official > official.sorted
sort -u spec.paperlean > paperlean.sorted
[ "$(wc -l < official.sorted)" -gt 15000 ] || fail "few specializations read"
comm -23 official.sorted paperlean.sorted | cut -d' ' -f2- | sort > only.official
comm -13 official.sorted paperlean.sorted | cut -d' ' -f2- | sort > only.paperlean
cat > hooked <<'EOF2'
Array.filterMapM._at_.Lean.Meta.SynthInstance.getInstances.spec_8
Lake.buildAction._at_._private.Lake.Build.Module.0.Lake.Module.buildLean.spec_0
Lean.Meta.whnfEasyCases._at_.Lean.Meta.whnfImp.spec_3
Lean.Meta.whnfEasyCases._at_._private.Lean.Meta.WHNF.0.Lean.Meta.whnfCore.go.spec_3
List.forIn'.loop._at_.Lean.Environment.addDeclCore.spec_1
List.forIn'.loop._at_._private.Lean.Environment.0.Lean.Environment.replayConsts.replayKernel.spec_3
WellFounded.opaqueFix₃._at_._private.Lean.Environment.0.Lean.setImportedEntries.spec_0
WellFounded.opaqueFix₃._at_._private.Lean.Meta.FunInfo.0.Lean.Meta.getFunInfoAux.spec_4
_private.Init.Data.Array.Basic.0.Array.foldlMUnsafe.fold._at_.Array.filterMapM._at_.Lean.Meta.SynthInstance.getInstances.spec_8.spec_11
_private.Init.Data.Array.Basic.0.Array.foldlMUnsafe.fold._at_._private.Lake.Build.Run.0.Lake.reportResult.spec_0
EOF2
$DIFF hooked only.official || fail "specializations of official Lean that PaperLean does not reuse"
$DIFF hooked only.paperlean || fail "specializations that official Lean does not have; PaperLean's own \
code must lie in the namespaces \`Lean.PaperLean\` and \`Lake.PaperLean\`, which the cache leaves out"

cat > Simple.lean <<'EOF2'
import Lean
open Lean
elab "ee" : term => return mkNatLit 3
example : (ee : Nat) = 3 := rfl
EOF2
cat > Math.lean <<'EOF2'
/-! A plain mathematical file: computable definitions next to theorems. -/
def Math.total (xs : List Nat) : Nat := xs.foldl (· + ·) 0
def Math.evens (n : Nat) : Array Nat := (Array.range n).filter (· % 2 == 0)
def Math.show (xs : List Nat) : String := toString (xs.map (· + 1))
structure Math.P where
  x : Nat
  y : Nat
  deriving Repr, BEq, Hashable, DecidableEq
theorem Math.total_nil : Math.total [] = 0 := rfl
EOF2
cat > All.lean <<'EOF2'
module
public import Lean.Elab.Tactic.Simp
import all Lean.Elab.Tactic.Simp
open Lean Meta Elab Tactic
/-! A `module` with `import all`, as `Batteries.Lean.Meta.Simp` is. -/
public def getCtx (stx : Syntax) : TacticM Simp.Context :=
  return (← mkSimpContext stx (eraseLocal := false)).ctx
public def names (xs : Array Name) : List String := (xs.map toString).toList
EOF2
mkdir official paperlean exact reuse
for f in Simple Math All; do
  "$OFFICIAL/bin/lean" $f.lean -o official/$f.olean -c official/$f.c > official/$f.out 2>&1 ||
    fail "official Lean does not compile $f.lean: $(cat official/$f.out)"
  lean $f.lean -o paperlean/$f.olean -c paperlean/$f.c > paperlean/$f.out 2>&1 ||
    fail "PaperLean does not compile $f.lean: $(cat paperlean/$f.out)"
  PAPERLEAN_EXACT=1 lean $f.lean -o exact/$f.olean -c exact/$f.c > exact/$f.out 2>&1 ||
    fail "PaperLean does not compile $f.lean with PAPERLEAN_EXACT"
  PAPERLEAN_REUSE=1 lean $f.lean -o reuse/$f.olean -c reuse/$f.c > reuse/$f.out 2>&1 ||
    fail "PaperLean does not compile $f.lean with reuse"
  for v in paperlean exact reuse; do
    cmp official/$f.c $v/$f.c || fail "the C code of $f.lean ($v) differs from official Lean's:
$($DIFF official/$f.c $v/$f.c | head -30)"
    cmp official/$f.out $v/$f.out || fail "the messages of $f.lean ($v) differ from official Lean's"
  done
done
