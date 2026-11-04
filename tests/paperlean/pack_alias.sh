# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# A symlink of a complete package root can use its pack. A directory symlinking only the package
# anchor must still read its own submodules, including when an alias changes between imports.

SRC="$TMP_DIR/src"
REAL="$TMP_DIR/real"
ALT="$TMP_DIR/alternate"
ALIAS="$TMP_DIR/alias"
mkdir -p "$SRC/AliasPkg" "$REAL/AliasPkg" "$ALT/AliasPkg"
cat > "$SRC/AliasPkg.lean" <<'EOF2'
/-! The package anchor shared by the alias fixtures. -/
namespace AliasPkg
def anchor : Nat := 0
end AliasPkg
EOF2
cat > "$SRC/AliasPkg/Value.lean" <<'EOF2'
import AliasPkg
/-! The original submodule stored in the pack. -/
namespace AliasPkg
def value : Nat := 1
end AliasPkg
EOF2
cd "$SRC"
run lean -o "$REAL/AliasPkg.olean" AliasPkg.lean
run env LEAN_PATH="$REAL" lean -o "$REAL/AliasPkg/Value.olean" AliasPkg/Value.lean
cat > "$TMP_DIR/pack.lean" <<'EOF2'
import Lean.PaperLean.OLeanPack
/-! Writes the package pack used by this regression. -/
def main (args : List String) : IO Unit := do
  let n ← Lean.PaperLean.OLeanPack.create #[args[1]!] args[0]!
  IO.println s!"packed: {n}"
EOF2
capture lean --run "$TMP_DIR/pack.lean" "$TMP_DIR/pkg.paperlean" "$REAL"
check_out_contains "packed: 2"
ln -s "$REAL" "$ALIAS"
ln -s "$REAL/AliasPkg.olean" "$ALT/AliasPkg.olean"
cat > "$SRC/AliasPkg/Value.lean" <<'EOF2'
import AliasPkg
/-! A different submodule under a directory sharing only the package anchor. -/
namespace AliasPkg
def value : Nat := 2
def onlyInV2 : Nat := 42
end AliasPkg
EOF2
run env LEAN_PATH="$ALT" lean -o "$ALT/AliasPkg/Value.olean" AliasPkg/Value.lean
cat > Use.lean <<'EOF2'
import AliasPkg.Value
/-! Observable output distinguishes the two physical submodules. -/
#eval AliasPkg.value
#check AliasPkg.anchor
EOF2
capture env LEAN_PATH="$ALIAS" LEAN_OLEAN_PACK= lean Use.lean
cp "$CAPTURED.out.produced" "$TMP_DIR/original.out"
check_out_contains "1"
capture env LEAN_PATH="$ALT" LEAN_OLEAN_PACK= lean Use.lean
cp "$CAPTURED.out.produced" "$TMP_DIR/alternate.out"
check_out_contains "2"
if $DIFF -- "$TMP_DIR/original.out" "$TMP_DIR/alternate.out" > /dev/null; then
  fail "the alternate submodule did not produce different output"
fi
for mode in fast check; do
  setting=""
  [ "$mode" = check ] && setting=check
  capture env LEAN_PATH="$ALIAS" LEAN_OLEAN_PACK="$TMP_DIR/pkg.paperlean" \
    PAPERLEAN_IMPORT="$setting" PAPERLEAN_IMPORT_TIMING=1 lean Use.lean
  check_out_contains "paperlean-timing modules.fast packed=2 "
  grep -v "^paperlean-" "$CAPTURED.out.produced" | $DIFF -- "$TMP_DIR/original.out" - ||
    fail "the whole-directory alias changed import output ($mode)"
  capture env LEAN_PATH="$ALT" LEAN_OLEAN_PACK="$TMP_DIR/pkg.paperlean" \
    PAPERLEAN_IMPORT="$setting" PAPERLEAN_IMPORT_TIMING=1 lean Use.lean
  check_out_contains "paperlean-timing modules.fallback (fast import not applicable: "
  grep -v "^paperlean-" "$CAPTURED.out.produced" | $DIFF -- "$TMP_DIR/alternate.out" - ||
    fail "a shared anchor caused the pack to supply the wrong submodule ($mode)"
done

cat > Retarget.lean <<'EOF2'
import Lean
open Lean
/-! Retargets one search-path directory between imports in the same process. -/
def version (env : Environment) : String :=
  s!"value present: {env.contains `AliasPkg.value}, v2: {env.contains `AliasPkg.onlyInV2}"
def main (args : List String) : IO Unit := do
  let [alias, next] := args | throw <| IO.userError "usage: <alias> <replacement>"
  initSearchPath (← findSysroot)
  IO.println s!"first: {version (← importModules #[{ module := `AliasPkg.Value }] {})}"
  IO.FS.rename next alias
  IO.println s!"second: {version (← importModules #[{ module := `AliasPkg.Value }] {})}"
EOF2
for mode in fast check; do
  setting=""
  [ "$mode" = check ] && setting=check
  ln -s "$REAL" "$TMP_DIR/retarget-$mode"
  ln -s "$ALT" "$TMP_DIR/next-$mode"
  capture env LEAN_PATH="$TMP_DIR/retarget-$mode" LEAN_OLEAN_PACK="$TMP_DIR/pkg.paperlean" \
    PAPERLEAN_IMPORT="$setting" PAPERLEAN_IMPORT_TIMING=1 \
    lean --run Retarget.lean "$TMP_DIR/retarget-$mode" "$TMP_DIR/next-$mode"
  check_out_contains "first: value present: true, v2: false"
  check_out_contains "second: value present: true, v2: true"
  check_out_contains "paperlean-timing modules.fast packed=2 "
  check_out_contains "paperlean-timing modules.fallback (fast import not applicable: "
done
