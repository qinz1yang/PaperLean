# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Temporary imports must not leave region-backed objects in thread-local lookup caches. Check the
# admission boundary, another lookup after region release, and a dedicated thread's cache teardown.

cat > "$TMP_DIR/TransientLookup.lean" <<'EOF2'
/-! A module imported only by the transient-lifetime regression. -/
namespace TransientLookup
def sentinel : Nat := 42
end TransientLookup
EOF2
cat > "$TMP_DIR/LookupLifetime.lean" <<'EOF2'
import Lean
open Lean

/-! Transient module regions end before the thread-local lookup cache does. -/

run_cmd do
  let env ← getEnv
  let table := env.constants.map₁
  let some (n, _) := table.toList.find? (fun (n, _) => n == ``Nat)
    | throwError "imported Nat missing"
  unless (env.find? n).isSome do throwError "Nat lookup failed"
  let cached := PaperLean.lookupProbe (α := Option ConstantInfo) 0 table () n
  unless cached.isSome do throwError "the process-lifetime lookup was not cached"

unsafe def transientLookup : IO Unit :=
  withImportModules #[{ module := `TransientLookup }] {} fun env => do
    let table := env.constants.map₁
    let some (n, _) := table.toList.find? (fun (n, _) => n == `TransientLookup.sentinel)
      | throw <| IO.userError "transient constant missing"
    unless (env.find? n).isSome do throw <| IO.userError "transient lookup failed"
    let cached := PaperLean.lookupProbe (α := Option ConstantInfo) 0
      table () n
    if cached.isSome then throw <| IO.userError "a transient lookup was cached"

unsafe def main : IO Unit := do
  -- The second callback runs on the same thread after the first has released its regions.
  transientLookup
  transientLookup
  -- A task's thread-local cache also ends after the callback has released its regions.
  let task ← IO.asTask transientLookup .dedicated
  IO.ofExcept (← IO.wait task)
  IO.println "ok"
EOF2
cd "$TMP_DIR"
export LEAN_PATH="$TMP_DIR${LEAN_PATH:+:$LEAN_PATH}"
capture_exit 0 lean TransientLookup.lean -o TransientLookup.olean
capture_exit 0 lean --run LookupLifetime.lean
check_out_contains "ok"
