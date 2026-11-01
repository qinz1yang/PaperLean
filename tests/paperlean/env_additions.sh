# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that PaperLean's modules add nothing to the environment of a file but themselves:
# - for every module of official Lean 4.35.0-rc3, what importing it brings, by each way of importing,
#   and the order of it, is official Lean's but for PaperLean's own modules (`env_additions.lean`);
# - they declare no instances (no global ones, and no `SizeOf` instances), which Lean's searches would
#   try (instances with metavariables in their problems take every instance of a class), taking other
#   names than official Lean's. For `import Lean` and for `import Lean.Elab.ElabRules` (whose closure
#   has fewer of Std's modules), every module of the environment that is not PaperLean's is reached
#   from the imports without passing through PaperLean's, and no instance of the instance index is
#   declared in PaperLean's modules.
# It needs official Lean, at `$OFFICIAL_LEAN_TOOLCHAIN` or elan's, and fails without it.
OFFICIAL=${OFFICIAL_LEAN_TOOLCHAIN:-$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3}
[ -d "$OFFICIAL/lib/lean/Lean" ] ||
  fail "official Lean 4.35.0-rc3 is not at $OFFICIAL (set OFFICIAL_LEAN_TOOLCHAIN to where it is)"

lean --run env_additions.lean "$OFFICIAL/lib/lean" "$BUILD_DIR/lib/lean" > "$TMP_DIR/closures.out" 2>&1 ||
  fail "env_additions.lean failed: $(head -20 "$TMP_DIR/closures.out")"
[ "$(grep -c . "$TMP_DIR/closures.out")" = 1 ] || fail "what imports bring differs from official Lean's:
$(head -20 "$TMP_DIR/closures.out" | cut -c1-300)"
[ "$(cut -d' ' -f1 "$TMP_DIR/closures.out")" -gt 2000 ] ||
  fail "few modules compared: $(cat "$TMP_DIR/closures.out")"

cd "$TMP_DIR"
for root in Lean Lean.Elab.ElabRules; do
  cat > Closure.lean <<EOF
import $root
open Lean Meta
/-- Whether \`m\` is one of PaperLean's modules. -/
def isPaperLean (m : Name) : Bool := (\`Lean.PaperLean).isPrefixOf m
#eval show MetaM Unit from do
  let env ← getEnv
  let names := env.header.moduleNames
  let mut idx : Std.HashMap Name Nat := {}
  for h : i in [0:names.size] do
    idx := idx.insert names[i] i
  -- (the modules reached from the imports, not through PaperLean's)
  let mut reached : NameSet := {}
  let mut todo := env.header.imports.toList.map (·.module)
  while true do
    let m :: rest := todo | break
    todo := rest
    if reached.contains m || isPaperLean m then continue
    reached := reached.insert m
    let some i := idx[m]? | continue
    todo := (env.header.moduleData[i]!.imports.toList.map (·.module)) ++ todo
  let mut n := 0
  for m in names do
    unless isPaperLean m || reached.contains m do
      IO.println s!"a module that PaperLean's add: {m}"
  for (inst, _) in (instanceExtension.getState env).instanceNames do
    if let some i := env.getModuleIdxFor? inst then
      if isPaperLean names[i]! then
        IO.println s!"an instance of PaperLean's module {names[i]!}: {inst}"
    n := n + 1
  IO.println s!"{n} instances"
EOF
  lean Closure.lean > closure.out 2>&1 || fail "Closure.lean ($root) failed: $(cat closure.out)"
  grep -q "^[0-9]* instances$" closure.out ||
    fail "Closure.lean ($root) did not run: $(cat closure.out)"
  if grep -q "PaperLean" closure.out; then fail "import $root: $(grep PaperLean closure.out)"; fi
done
