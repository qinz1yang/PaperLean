# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Runs `graph_diff.lean`, which tests the object-graph comparison behind `PAPERLEAN_IMPORT=check`
# and prints nothing if it passes.
capture lean graph_diff.lean
$DIFF -- /dev/null "$CAPTURED.out.produced" || fail "unexpected output"
