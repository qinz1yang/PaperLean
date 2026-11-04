# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests the cache of each thread for lookups of names in the tables of the imported modules
# (`Lean.PaperLean.cachedLookup`, `src/paperlean/lookup_cache.cpp`), which takes only persistent
# names: for every imported constant, `Environment.find?`, `findAsync?`, `findConstVal?`, the
# reducibility status and the tags of `auxRecExt`, `protectedExt` and `noncomputableExt`, asked
# twice with the constant's name of the imported module (stored, then found in the cache), give what
# they give for a fresh copy of the name, which the cache does not take; so do names that are not
# imported (binder names of imported types). The lookups interleave, so that entries of different
# kinds and tables share the cache.

cat > "$TMP_DIR/LookupCache.lean" <<'EOF2'
import Lean
open Lean

/-- A copy of `n` made of new objects, which the cache does not take. -/
def copyName : Name → Name
  | .anonymous => .anonymous
  | .str p s => .str (copyName p) s
  | .num p k => .num (copyName p) k

def answers (env : Environment) (n : Name) : String :=
  s!"{(env.find? n).map (·.name)} {(env.findAsync? n).map (·.name)} \
    {(env.findConstVal? n).map (·.name)} {repr (getReducibilityStatusCore env n)} \
    {isAuxRecursor env n} {isProtected env n} {isNoncomputable env n}"

run_cmd do
  unless PaperLean.nativeAvailable (← getEnv) do
    throwError "PaperLean's native code is not available"
  let env ← getEnv
  let mut checked : Nat := 0
  let mut differ : Array Name := #[]
  let consts := env.constants.map₁.toList
  -- (binder names: persistent names that are not imported constants)
  let binders := consts.filterMap fun (_, c) => if let .forallE b .. := c.type then some b else none
  let names := consts.map (·.1) ++ binders ++ consts.map (·.1.str "notImported")
  for round in [0, 1] do
    for n in names do
      let fresh := copyName n
      checked := checked + 1
      unless answers env n == answers env fresh do
        differ := differ.push n
    unless round == 1 || checked > 100000 do
      throwError "too few names checked: {checked}"
  unless differ.isEmpty do
    throwError "different answers for {differ.size} names, e.g. {differ.toList.take 5}"
  logInfo "ok"
EOF2
cd "$TMP_DIR"
capture_exit 0 lean LookupCache.lean
check_out_contains "ok"
