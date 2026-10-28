# Runs `setup_import_arts.lean`, which tests the encoding of `ModuleSetup.importArts` and prints
# nothing if it passes.
capture lean setup_import_arts.lean
$DIFF -- /dev/null "$CAPTURED.out.produced" || fail "unexpected output"
