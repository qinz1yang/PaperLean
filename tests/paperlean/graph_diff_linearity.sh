# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# `Lean.PaperLean.graphDiff` (`PAPERLEAN_IMPORT=check`) compares the linearity mark of arrays,
# scalar arrays and strings: two graphs that differ only in that bit are not equal. The marks are
# runtime state that decides whether an update may mutate in place; a fast-import defect that adds
# or drops one must not pass the check.
run lean --run "$TEST_DIR/paperlean/graph_diff_linearity.lean"
