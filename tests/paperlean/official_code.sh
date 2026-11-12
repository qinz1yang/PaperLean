# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that files that see the specializations of imported modules, non-module files and `module`s
# with `import all`, do not import a PaperLean-only specialization and that the C they generate
# refers only to symbols official Lean 4.35.0-rc3 has:
# - the compiler's cache of specializations (`official_code.lean`) has no PaperLean-only upstream
#   specialization name (the O13 regression list below is the current boundary);
# - the C code of such files, with specializations that the cache has, declares only external `l_`
#   symbols official Lean exports; the messages are identical.
# It needs official Lean, at `$OFFICIAL_LEAN_TOOLCHAIN` or elan's, and fails without it.
OFFICIAL=${OFFICIAL_LEAN_TOOLCHAIN:-$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3}
[ -x "$OFFICIAL/bin/lean" ] ||
  fail "official Lean 4.35.0-rc3 is not at $OFFICIAL (set OFFICIAL_LEAN_TOOLCHAIN to where it is)"
# (the ABI contract: no PaperLean-only specialization name may enter the imported cache, and every
# external symbol the C code declares must exist in official Lean's libraries; which official-only
# specialization PaperLean chooses not to reuse is an implementation choice)
externals() {
  grep -E '^(extern )?[a-z_0-9]+\*? (l|lean)_[A-Za-z0-9_]+(\(.*\))?;$' "$1" | sed -E 's/^extern //' | sort -u
}
syms() {
  for l in "$1"/lib/lean/lib*.so "$1"/lib/lean/lib*.dylib; do
    [ -f "$l" ] || continue
    if [[ "$(uname)" == Darwin ]]; then
      nm -gU "$l" | awk '{print $3}' | sed 's/^_//'
    else
      nm -D --defined-only "$l" | awk '$2 ~ /[TDBR]/ {print $3}'
    fi
  done | grep -E '^(l_|lp_|lean_|initialize_)' | sort -u
}
check_externals() { # <c-file> <label>
  externals "$1" | awk '{print $2}' | sed -E 's/[;(].*//' | grep -E '^(l_|lp_)' | sort -u > "$1.produced.out"
  comm -23 "$1.produced.out" official.syms > "$1.missing.out"
  [ ! -s "$1.missing.out" ] ||
    fail "$2 refers to symbols that official Lean does not export, e.g.
$(head -20 "$1.missing.out")"
}

cp official_code.lean "$TMP_DIR/"
cd "$TMP_DIR"
syms "$OFFICIAL" > official.syms
[ "$(wc -l < official.syms)" -gt 100000 ] || fail "few symbols found in official Lean's libraries"
export LC_ALL=C

"$OFFICIAL/bin/lean" --run official_code.lean "$OFFICIAL/lib/lean" spec.official ||
  fail "official Lean cannot read its cache of specializations"
LEAN_PATH= lean --run official_code.lean "$BUILD_DIR/lib/lean" spec.paperlean ||
  fail "PaperLean cannot read its cache of specializations"
sort -u spec.official > official.sorted
sort -u spec.paperlean > paperlean.sorted
[ "$(wc -l < official.sorted)" -gt 15000 ] || fail "few specializations read"
# Compare declaration names, not `<key-hash> <name>` lines: a name can legitimately have a
# different specialization key in the two builds, while a name absent from official Lean's cache is
# a real leak if PaperLean-compiled code can reuse it.
cut -d' ' -f2- official.sorted | sort -u > official.names
cut -d' ' -f2- paperlean.sorted | sort -u > paperlean.names
comm -23 official.names paperlean.names > only.official.names
comm -13 official.names paperlean.names > only.paperlean.names
# (PaperLean-only cache names are usually the script's own local specializations; the ABI gate is
# the external symbols of the generated C below.  The O13 list is the library-cache regression:
# these 22 entries were generated in upstream modules after SpecExclusions was last regenerated.)
cat > o13.names <<'EOF2'
Lean.PersistentHashMap.find?._at_.Lean.SMap.find?._at_._private.Lean.KeyedDeclsAttribute.0.Lean.KeyedDeclsAttribute.addBuiltinEntry.spec_0.spec_0
Lean.PersistentHashMap.findAtAux._at_.Lean.PersistentHashMap.findAux._at_.Lean.PersistentHashMap.find?._at_.Lean.SMap.find?._at_._private.Lean.KeyedDeclsAttribute.0.Lean.KeyedDeclsAttribute.addBuiltinEntry.spec_0.spec_0.spec_1.spec_2
Lean.PersistentHashMap.findAux._at_.Lean.PersistentHashMap.find?._at_.Lean.SMap.find?._at_._private.Lean.KeyedDeclsAttribute.0.Lean.KeyedDeclsAttribute.addBuiltinEntry.spec_0.spec_0.spec_1
Lean.PersistentHashMap.insert._at_.Lean.SMap.insert._at_._private.Lean.KeyedDeclsAttribute.0.Lean.KeyedDeclsAttribute.registerBuiltinEntries.spec_0.spec_0
Lean.PersistentHashMap.insertAtCollisionNode._at_.Lean.PersistentHashMap.insertAux._at_.Lean.PersistentHashMap.insert._at_.Lean.SMap.insert._at_._private.Lean.KeyedDeclsAttribute.0.Lean.KeyedDeclsAttribute.registerBuiltinEntries.spec_0.spec_0.spec_1.spec_2
Lean.PersistentHashMap.insertAtCollisionNodeAux._at_.Lean.PersistentHashMap.insertAtCollisionNode._at_.Lean.PersistentHashMap.insertAux._at_.Lean.PersistentHashMap.insert._at_.Lean.SMap.insert._at_._private.Lean.KeyedDeclsAttribute.0.Lean.KeyedDeclsAttribute.registerBuiltinEntries.spec_0.spec_0.spec_1.spec_2.spec_4
Lean.PersistentHashMap.insertAux._at_.Lean.PersistentHashMap.insert._at_.Lean.SMap.insert._at_._private.Lean.KeyedDeclsAttribute.0.Lean.KeyedDeclsAttribute.registerBuiltinEntries.spec_0.spec_0.spec_1
Lean.SMap.find?._at_._private.Lean.KeyedDeclsAttribute.0.Lean.KeyedDeclsAttribute.addBuiltinEntry.spec_0
Lean.SMap.insert._at_._private.Lean.KeyedDeclsAttribute.0.Lean.KeyedDeclsAttribute.registerBuiltinEntries.spec_0
List.any._at_._private.Lean.Parser.Extension.0.Lean.Parser.updateBuiltinTokens.spec_0
List.foldl._at_._private.Lean.KeyedDeclsAttribute.0.Lean.KeyedDeclsAttribute.mkStateOfEntries.spec_0
List.forIn'.loop._at_._private.Lean.Parser.Extension.0.Lean.Parser.buildBuiltinTokenTable.spec_0
List.forIn'.loop._at_._private.Lean.Parser.Extension.0.Lean.Parser.buildBuiltinTokenTable.spec_1
Std.DHashMap.Internal.AssocList.contains._at_.Std.DHashMap.Internal.Raw₀.insert._at_.Lean.SMap.insert._at_._private.Lean.KeyedDeclsAttribute.0.Lean.KeyedDeclsAttribute.registerBuiltinEntries.spec_0.spec_1.spec_3
Std.DHashMap.Internal.AssocList.foldlM._at_._private.Std.Data.DHashMap.Internal.Defs.0.Std.DHashMap.Internal.Raw₀.expand.go._at_.Std.DHashMap.Internal.Raw₀.expand._at_.Std.DHashMap.Internal.Raw₀.insert._at_.Lean.SMap.insert._at_._private.Lean.KeyedDeclsAttribute.0.Lean.KeyedDeclsAttribute.registerBuiltinEntries.spec_0.spec_1.spec_4.spec_7.spec_9
Std.DHashMap.Internal.AssocList.get?._at_.Std.DHashMap.Internal.Raw₀.Const.get?._at_.Lean.SMap.find?._at_._private.Lean.KeyedDeclsAttribute.0.Lean.KeyedDeclsAttribute.addBuiltinEntry.spec_0.spec_1.spec_3
Std.DHashMap.Internal.AssocList.replace._at_.Std.DHashMap.Internal.Raw₀.insert._at_.Lean.SMap.insert._at_._private.Lean.KeyedDeclsAttribute.0.Lean.KeyedDeclsAttribute.registerBuiltinEntries.spec_0.spec_1.spec_5
Std.DHashMap.Internal.Raw₀.Const.get?._at_.Lean.SMap.find?._at_._private.Lean.KeyedDeclsAttribute.0.Lean.KeyedDeclsAttribute.addBuiltinEntry.spec_0.spec_1
Std.DHashMap.Internal.Raw₀.expand._at_.Std.DHashMap.Internal.Raw₀.insert._at_.Lean.SMap.insert._at_._private.Lean.KeyedDeclsAttribute.0.Lean.KeyedDeclsAttribute.registerBuiltinEntries.spec_0.spec_1.spec_4
Std.DHashMap.Internal.Raw₀.insert._at_.Lean.SMap.insert._at_._private.Lean.KeyedDeclsAttribute.0.Lean.KeyedDeclsAttribute.registerBuiltinEntries.spec_0.spec_1
_private.Lean.Data.PersistentHashMap.0.Lean.PersistentHashMap.insertAux.traverse._at_.Lean.PersistentHashMap.insertAux._at_.Lean.PersistentHashMap.insert._at_.Lean.SMap.insert._at_._private.Lean.KeyedDeclsAttribute.0.Lean.KeyedDeclsAttribute.registerBuiltinEntries.spec_0.spec_0.spec_1.spec_3
_private.Std.Data.DHashMap.Internal.Defs.0.Std.DHashMap.Internal.Raw₀.expand.go._at_.Std.DHashMap.Internal.Raw₀.expand._at_.Std.DHashMap.Internal.Raw₀.insert._at_.Lean.SMap.insert._at_._private.Lean.KeyedDeclsAttribute.0.Lean.KeyedDeclsAttribute.registerBuiltinEntries.spec_0.spec_1.spec_4.spec_7
EOF2
sort -u o13.names > o13.sorted
comm -12 o13.sorted paperlean.names > o13.present
[ ! -s o13.present ] || fail "O13 specializations are still in the imported cache; regenerate SpecExclusions:
$(cat o13.present)"

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
    check_externals $v/$f.c "$f.lean ($v)"
    cmp official/$f.out $v/$f.out || fail "the messages of $f.lean ($v) differ from official Lean's"
  done
done
