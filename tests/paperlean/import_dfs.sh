# Differential test for the import traversal (`importModulesCore`): a small module graph with
# public/private/meta/all edges, diamonds that force flag bumps and closure re-traversals, a module
# without IR files, and a missing `.olean`.  The same roots are run under PAPERLEAN_IMPORT=legacy
# (the original folds), the default (the faster implementation), and PAPERLEAN_IMPORT=check (which
# builds both); the observable imported environment and all errors must be identical.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK
# Extra environment of the runs; set below to use an olean pack of the modules.
EXTRA_ENV=()
SRC="$TMP_DIR/src"
LIB="$TMP_DIR/lib"
mkdir -p "$SRC/Mod" "$LIB/Mod"

# Writes the probe used by both successful roots.  It prints the effective import of every module
# in the order of `env.header.moduleNames`, followed by the number of compacted regions.
emit_probe() {
  cat <<'EOF'

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  IO.println s!"modules={env.header.modules.size} regions={env.header.regions.size}"
  for i in [0:env.header.modules.size] do
    let m := env.header.modules[i]!
    let phase := match m.irPhases with
      | .runtime => "runtime"
      | .comptime => "comptime"
      | .all => "all"
    IO.println s!"module {i} name={env.header.moduleNames[i]!} module={m.module} importAll={m.importAll} isExported={m.isExported} isMeta={m.isMeta} irPhases={phase} hasData={m.hasData}"
EOF
}

# Leaves whose flags are changed by later visits.
cat > "$SRC/Mod/Leaf.lean" <<'EOF'
module

public def leaf : Nat := 1
EOF

cat > "$SRC/Mod/Child.lean" <<'EOF'
module

public import Mod.Leaf

public def child : Nat := leaf + 1
EOF

cat > "$SRC/Mod/Diamond.lean" <<'EOF'
module

public import Mod.Child
public import Mod.Leaf

public def diamond : Nat := child + leaf
EOF

# FirstParent reaches Diamond through a non-exported, non-meta edge (but with importAll on, so the
# data is loaded).  SecondParent reaches it through a public edge, which must bump Diamond and
# re-traverse Diamond's closure (Child and Leaf).
cat > "$SRC/Mod/FirstParent.lean" <<'EOF'
module

import Mod.Diamond
EOF

cat > "$SRC/Mod/SecondParent.lean" <<'EOF'
module

public import Mod.Diamond
EOF

cat > "$SRC/Mod/Late.lean" <<'EOF'
module

public def late : Nat := 6
EOF

# LateParent is first imported without `import all`.  Its private `import Mod.Late` is skipped
# then, so Late is absent from the map.  A later `import all Mod.BumpParent`, whose own edge is
# `import all Mod.LateParent`, bumps LateParent and re-traverses its closure; Late is discovered
# during that bump and must be appended after LateParent (the bump inserts the parent before
# re-traversing it).
cat > "$SRC/Mod/LateParent.lean" <<'EOF'
module

import Mod.Late
EOF

# A parent used only to revisit LateParent with `import all`; the skipped Late edge must then be
# reached during the bump of LateParent.
cat > "$SRC/Mod/BumpParent.lean" <<'EOF'
module

import all Mod.LateParent
EOF

cat > "$SRC/Mod/AllChild.lean" <<'EOF'
module

public def allChild : Nat := 2
EOF

cat > "$SRC/Mod/AllTarget.lean" <<'EOF'
module

public import Mod.AllChild
import all Mod.AllChild

public def allTarget : Nat := allChild + 1
EOF

cat > "$SRC/Mod/PublicAllTarget.lean" <<'EOF'
module

public import Mod.Leaf
import all Mod.Leaf

public def publicAllTarget : Nat := leaf + 2
EOF

cat > "$SRC/Mod/MetaLeaf.lean" <<'EOF'
module

public def metaLeaf : Nat := 3
EOF

# MetaLeaf is first discovered through `meta import`, hence with phase `.comptime` and isMeta=true.
# PlainMetaParent later reaches it through a public plain edge, whose edge phase is `.runtime`;
# comparing that with the stored `.comptime` turns the phase into `.all` (the join of edge phases).
# PublicMetaParent (public meta) and MetaAllParent (public import all) then keep/confirm `.all`.
cat > "$SRC/Mod/MetaFirstParent.lean" <<'EOF'
module

meta import Mod.MetaLeaf
EOF

cat > "$SRC/Mod/PublicMetaParent.lean" <<'EOF'
module

public meta import Mod.MetaLeaf
EOF

cat > "$SRC/Mod/PlainMetaParent.lean" <<'EOF'
module

public import Mod.MetaLeaf
EOF

cat > "$SRC/Mod/MetaAllParent.lean" <<'EOF'
module

public import Mod.MetaLeaf
import all Mod.MetaLeaf
EOF

# A `meta import` of MetaTop, whose private import of MetaMid (and MetaMid's of MetaDeep) is then
# needed for IR only: MetaMid and MetaDeep are imported without data, and the traversal continues
# through the imports of their IR parts.
cat > "$SRC/Mod/MetaDeep.lean" <<'EOF'
module

public def metaDeep : Nat := 7
EOF

cat > "$SRC/Mod/MetaMid.lean" <<'EOF'
module

import Mod.MetaDeep

public def metaMid : Nat := 8
EOF

cat > "$SRC/Mod/MetaTop.lean" <<'EOF'
module

import Mod.MetaMid

public def metaTop : Nat := 9
EOF

cat > "$SRC/Mod/NoIR.lean" <<'EOF'
module

public def noIR : Nat := 4
EOF

cat > "$SRC/Mod/Gone.lean" <<'EOF'
module

public def gone : Nat := 5
EOF

# Non-`module` files importing module files.
cat > "$SRC/Mod/PlainA.lean" <<'EOF'
import Mod.Leaf
import Mod.Diamond
EOF

cat > "$SRC/Mod/PlainB.lean" <<'EOF'
import Mod.PlainA
import Mod.MetaLeaf
EOF

# Compile from the source root so Lean infers the module names `Mod.X` from the file paths.
cd "$SRC"

# Compile in dependency order.  `module` files additionally produce `.olean.server`,
# `.olean.private`, `.ir.sig`, and `.ir`; a non-`module` file produces only `.olean`.
for m in \
  Mod/Leaf Mod/Child Mod/Diamond Mod/FirstParent Mod/SecondParent Mod/Late Mod/LateParent Mod/BumpParent \
  Mod/AllChild Mod/AllTarget Mod/PublicAllTarget \
  Mod/MetaLeaf Mod/MetaFirstParent Mod/PublicMetaParent Mod/PlainMetaParent Mod/MetaAllParent \
  Mod/MetaDeep Mod/MetaMid Mod/MetaTop \
  Mod/NoIR Mod/Gone Mod/PlainA Mod/PlainB
do
  mkdir -p "$(dirname "$LIB/$m.olean")"
  run env LEAN_PATH="$LIB" lean -Dcompiler.postponeCompile=false \
    -o "$LIB/$m.olean" -i "$LIB/$m.ilean" "$m.lean"
done

for ext in olean olean.server olean.private ir.sig ir; do
  [ -f "$LIB/Mod/Leaf.$ext" ] ||
    fail "expected module compilation to produce Mod/Leaf.$ext"
done
[ -f "$LIB/Mod/PlainA.olean" ] || fail "expected Mod/PlainA.olean"

# A module whose IR files are absent.  Deleting both files after a normal compile also covers the
# `writeIR := false` / leanir-not-run producer state, without changing the .olean parts.
rm -f "$LIB/Mod/NoIR.ir" "$LIB/Mod/NoIR.ir.sig"

cat > "$SRC/RootMod.lean" <<'EOF'
module

import Mod.LateParent
import all Mod.FirstParent
public import Mod.SecondParent

import all Mod.MetaFirstParent
public import Mod.PlainMetaParent
public import Mod.PublicMetaParent
public import Mod.MetaAllParent

import all Mod.AllTarget
public import Mod.PublicAllTarget
import all Mod.PublicAllTarget
import all Mod.NoIR

import all Mod.BumpParent

meta import Mod.MetaTop

meta import Lean.CoreM
meta import Lean.MonadEnv
EOF
emit_probe >> "$SRC/RootMod.lean"

cat > "$SRC/RootPlain.lean" <<'EOF'
import Lean.CoreM
import Lean.MonadEnv
import Mod.Leaf
import Mod.LateParent
import Mod.PlainA
import Mod.PlainB
import Mod.NoIR
import Mod.PublicAllTarget
import Mod.MetaAllParent
import Mod.Diamond
EOF
emit_probe >> "$SRC/RootPlain.lean"

cat > "$SRC/BadModuleRoot.lean" <<'EOF'
module

import Mod.PlainA
EOF

cat > "$SRC/MissingRoot.lean" <<'EOF'
import Mod.Gone
EOF

# Runs a successful root in all three modes and compares the complete output.
run_root() {
  local name="$1" expect="$2" mode
  for mode in "" legacy check; do
    capture env LEAN_PATH="$LIB" PAPERLEAN_IMPORT="$mode" "${EXTRA_ENV[@]}" lean "$name.lean"
    check_out_contains "modules="
    check_out_contains "regions="
    check_out_contains "$expect"
    cp "$CAPTURED.out.produced" "$TMP_DIR/$name.$mode.out"
  done
  $DIFF -- "$TMP_DIR/$name..out" "$TMP_DIR/$name.legacy.out" ||
    fail "output of $name differs from the legacy import"
  $DIFF -- "$TMP_DIR/$name..out" "$TMP_DIR/$name.check.out" ||
    fail "output of $name differs under PAPERLEAN_IMPORT=check"
}

# Runs a root that must fail in all three modes, checks its message, and compares the output.
run_failing_root() {
  local name="$1" expect="$2" mode
  for mode in "" legacy check; do
    capture_fail env LEAN_PATH="$LIB" PAPERLEAN_IMPORT="$mode" "${EXTRA_ENV[@]}" lean "$name.lean"
    check_out_contains "$expect"
    cp "$CAPTURED.out.produced" "$TMP_DIR/$name.$mode.out"
  done
  $DIFF -- "$TMP_DIR/$name..out" "$TMP_DIR/$name.legacy.out" ||
    fail "output of $name differs from the legacy import"
  $DIFF -- "$TMP_DIR/$name..out" "$TMP_DIR/$name.check.out" ||
    fail "output of $name differs under PAPERLEAN_IMPORT=check"
}

run_root RootMod Mod.MetaLeaf
check_out_contains "name=Mod.Late "
check_out_contains "name=Mod.MetaDeep "
run_root RootPlain Mod.PlainB
check_out_contains "name=Mod.Late "
run_failing_root BadModuleRoot 'cannot import non-`module` Mod.PlainA from `module`'

# The same with the modules in an olean pack, whose module table the import then uses.
cat > "$TMP_DIR/pack.lean" <<'END'
import Lean.PaperLean.OLeanPack
def main (args : List String) : IO Unit := do
  let n ← Lean.PaperLean.OLeanPack.create #[args[1]!] args[0]!
  IO.println s!"packed: {decide (n > 0)}"
END
capture lean --run "$TMP_DIR/pack.lean" "$TMP_DIR/mods.paperlean" "$LIB"
check_out_contains "packed: true"
for name in RootMod RootPlain BadModuleRoot; do
  cp "$TMP_DIR/$name..out" "$TMP_DIR/$name.nopack.out"
done
EXTRA_ENV=(LEAN_OLEAN_PACK="$TMP_DIR/mods.paperlean")
run_root RootMod Mod.MetaLeaf
run_root RootPlain Mod.PlainB
run_failing_root BadModuleRoot 'cannot import non-`module` Mod.PlainA from `module`'
for name in RootMod RootPlain BadModuleRoot; do
  $DIFF -- "$TMP_DIR/$name.nopack.out" "$TMP_DIR/$name..out" || fail "output of $name differs with the pack"
done
for name in RootPlain RootMod; do
  capture env LEAN_PATH="$LIB" LEAN_OLEAN_PACK="$TMP_DIR/mods.paperlean" PAPERLEAN_IMPORT_TIMING=1 lean "$name.lean"
  check_out_matches "paperlean-timing modules.fast packed=[1-9]"
done

# Delete the main `.olean` of a dotted module, leaving its package directory in place.  findOLean
# returns the candidate path without checking the leaf file, so the reader's existence check is
# what reports the error (rather than "unknown module prefix").
rm -f "$LIB/Mod/Gone.olean"
EXTRA_ENV=()
run_failing_root MissingRoot 'of module Mod.Gone does not exist'
# The packed copy of the deleted file is not used.
EXTRA_ENV=(LEAN_OLEAN_PACK="$TMP_DIR/mods.paperlean")
run_failing_root MissingRoot 'of module Mod.Gone does not exist'
