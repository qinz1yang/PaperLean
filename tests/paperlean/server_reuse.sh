# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests where `lean` may reuse results (`Lean.PaperLean.Speculation.onElabThread`): in the frontend of
# the command-line `lean`, the first of its process, and in no other frontend. Not in the language
# server's worker, where an elaboration after an edit may run while a cancelled one still does, nor in
# a frontend that a command or a program starts, also one that does not go through
# `Lean.Elab.runFrontend` (`Lean.Elab.process`), which turns reuse off from there on, with a message.

export PAPERLEAN_REUSE=1

cd "$TMP_DIR"
cat > Server.lean <<'EOF2'
import Lean
#eval Lean.PaperLean.Speculation.onElabThread
--^ collectDiagnostics
EOF2
lean Server.lean > cmdline.out 2>&1 || fail "Server.lean failed: $(cat cmdline.out)"
grep -qx "true" cmdline.out || fail "the command-line lean does not reuse: $(cat cmdline.out)"
lean -Dlinter.all=false --run "$(dirname "$FILE")/../server_interactive/run_test.lean" Server.lean \
  > server.out 2>&1 || fail "the server test failed: $(cat server.out)"
grep -q '"message": "false' server.out || fail "the server reuses: $(cat server.out)"

# a frontend that a command starts
cat > Nested.lean <<'EOF2'
import Lean
open Lean Elab Command
#eval Lean.PaperLean.Speculation.onElabThread
#eval show CommandElabM Unit from do
  let (_, msgs) ← Lean.Elab.process "#eval Lean.PaperLean.Speculation.onElabThread" (← getEnv) {}
    "Inner.lean"
  for m in msgs.toList do IO.println s!"inner: {← m.data.toString}"
#eval Lean.PaperLean.Speculation.onElabThread
EOF2
printf 'true\ninner: false\nfalse\n' > nested.expected
lean Nested.lean > nested.out 2> nested.err || fail "Nested.lean failed: $(cat nested.out nested.err)"
# (a message may end with a line break)
grep -v '^$' nested.out > nested.lines
$DIFF -- nested.expected nested.lines || fail "a frontend that a command starts reuses"
grep -qx "PaperLean: a further frontend in this process (Inner.lean): reuse of results and its oracle are off from here on" nested.err ||
  fail "Nested.lean did not say that reuse is off: $(cat nested.err)"

# a frontend that a program starts after the module's elaboration
cat > Driver.lean <<'EOF2'
import Lean
open Lean Elab
unsafe def main : IO Unit := do
  IO.println s!"main: {← Lean.PaperLean.Speculation.onElabThread}"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `Lean }] {} (loadExts := true)
  let (_, msgs) ← Lean.Elab.process "#eval Lean.PaperLean.Speculation.onElabThread" env {}
    "Driven.lean"
  for m in msgs.toList do IO.println s!"inner: {← m.data.toString}"
EOF2
printf 'main: false\ninner: false\n' > driver.expected
lean --run Driver.lean > driver.out 2> driver.err || fail "Driver.lean failed: $(cat driver.out driver.err)"
grep -v '^$' driver.out > driver.lines
$DIFF -- driver.expected driver.lines || fail "a frontend that a program starts reuses"
grep -qx "PaperLean: a further frontend in this process (Driven.lean): reuse of results and its oracle are off from here on" driver.err ||
  fail "Driver.lean did not say that reuse is off: $(cat driver.err)"
