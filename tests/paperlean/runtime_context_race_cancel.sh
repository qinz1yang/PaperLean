# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# `ContextAsync.race` must cancel the losing computation's context when the winner
# returns, even when the loser is blocked in a noncooperative operation.  The old
# implementation used the `ContextAsync.async` wrapper, which left an extra context
# (and the loser's explicit context) alive until the loser eventually finished.
case "$(uname -s)" in
  Darwin|Linux)
    run python3 "$TEST_DIR/paperlean/runtime_common/run_with_timeout.py" --timeout 50 -- env LEAN_NUM_THREADS=1 lean --run "$TEST_DIR/paperlean/runtime_context_race_cancel/RaceScope.lean"
    run python3 "$TEST_DIR/paperlean/runtime_common/run_with_timeout.py" --timeout 50 -- env LEAN_NUM_THREADS=4 lean --run "$TEST_DIR/paperlean/runtime_context_race_cancel/RaceScope.lean"
    ;;
esac
