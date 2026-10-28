# Runs `graph_diff.lean`, which tests the object-graph comparison behind `PAPERLEAN_IMPORT=check`
# and prints nothing if it passes.
capture lean graph_diff.lean
$DIFF -- /dev/null "$CAPTURED.out.produced" || fail "unexpected output"
