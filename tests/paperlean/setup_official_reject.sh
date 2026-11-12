# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# An indexed side setup must not decode as an official `ModuleSetup`: official Lean would ignore
# the anonymous index reference, use an effectively empty `importArts`, and silently select imports
# from `LEAN_PATH` (possibly another package's same-named module). The official decoder must reject
# the side file; PaperLean's own decoder must still recover the reference and resolve it.
OFFICIAL=${OFFICIAL_LEAN_TOOLCHAIN:-$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3}
[ -x "$OFFICIAL/bin/lean" ] || fail "official Lean 4.35.0-rc3 is not at $OFFICIAL"
SIDE="$TMP_DIR/M.setup.paperlean"
run lean --run "$TEST_DIR/paperlean/setup_official_reject.lean" write "$SIDE"
printf 'def m : Nat := 1\n' > "$TMP_DIR/M.lean"
# Official Lean 4.35.0-rc3 must not run with the setup; on the current code it accepts the
# anonymous entry as an ordinary (unused) import and compiles M from the search path.
capture_fail env LEAN_PATH="$TMP_DIR" "$OFFICIAL/bin/lean" --setup "$SIDE" "$TMP_DIR/M.lean"
check_out_contains "failed to load header"
# The unit check also requires PaperLean's own decoder to keep reading the reference.
run lean --run "$TEST_DIR/paperlean/setup_official_reject.lean"
