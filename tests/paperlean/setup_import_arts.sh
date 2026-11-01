# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Runs `setup_import_arts.lean`, which tests the encoding of `ModuleSetup.importArts` and prints
# nothing if it passes.
capture lean setup_import_arts.lean
$DIFF -- /dev/null "$CAPTURED.out.produced" || fail "unexpected output"
