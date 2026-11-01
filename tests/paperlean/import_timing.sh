# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that `PAPERLEAN_IMPORT_TIMING` reports the CPU time of the process between two marks, which
# cannot be negative. Marks come from more than one thread: with a thread's own clock and one baseline,
# a mark compares the times of two threads, and the first one, on the import's thread, is below zero.

echo 'import Lean' > "$TMP_DIR/Timing.lean"
capture env PAPERLEAN_IMPORT_TIMING=1 lean "$TMP_DIR/Timing.lean"
check_out_contains "paperlean-timing start "
if grep " cpu=-" "$CAPTURED.out.produced"; then
  fail "a mark reports negative CPU time"
fi
