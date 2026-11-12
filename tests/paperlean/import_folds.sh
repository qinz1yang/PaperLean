# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests the extension import folds that the import starts on another thread, before the extensions
# registered before them are finalized (`pureImportedFolds` in `Lean.PaperLean.Import`): under
# `PAPERLEAN_IMPORT_CHECK_FOLDS=1` the state of each is compared with the one `addImportedFn`
# computes on the importing thread (they must be the same objects), the import's results and errors
# are those of the import without them, and the extensions that this patch added are really started
# there (and nowhere when `PAPERLEAN_IMPORT=legacy` or `PAPERLEAN_IMPORT_THREADS=0`).

SRC="$TMP_DIR/src"
mkdir -p "$SRC"
cd "$SRC"

# `import Lean` imports the modules whose extensions these folds build states for: Lean's error
# explanations, its `@[grind]`, `@[ext]`, `@[congr]`, `@[csimp]` and `@[cbv_eval]` lemmas, classes,
# `export` aliases, namespaces and matcher information.
cat > Use.lean <<'END'
import Lean
#check Lean.Environment
END

# The folds off the importing thread, on it (`legacy`), and with the comparison of the two states:
# the same output.
capture env PAPERLEAN_IMPORT=legacy lean Use.lean
cp "$CAPTURED.out.produced" "$TMP_DIR/use.legacy.out"
capture env lean Use.lean
$DIFF -- "$TMP_DIR/use.legacy.out" "$CAPTURED.out.produced" ||
  fail "output of the import differs from the legacy import"
capture env PAPERLEAN_IMPORT=check lean Use.lean
$DIFF -- "$TMP_DIR/use.legacy.out" "$CAPTURED.out.produced" ||
  fail "output of the import differs under PAPERLEAN_IMPORT=check"
capture env PAPERLEAN_IMPORT=check PAPERLEAN_IMPORT_CHECK_FOLDS=1 lean Use.lean
$DIFF -- "$TMP_DIR/use.legacy.out" "$CAPTURED.out.produced" ||
  fail "a state built on another thread differs from the state addImportedFn computes"
# The comparison runs and reports a defect: the state of the background fold is corrupted for the
# test. `PAPERLEAN_IMPORT=check` alone does not run it.
capture_fail env PAPERLEAN_IMPORT=check PAPERLEAN_IMPORT_CHECK_FOLDS=1 \
  PAPERLEAN_IMPORT_CHECK_FAULT=fold lean Use.lean
check_out_contains "the state of \`addImportedFn\` of "
capture env PAPERLEAN_IMPORT=check PAPERLEAN_IMPORT_CHECK_FAULT=fold lean Use.lean
$DIFF -- "$TMP_DIR/use.legacy.out" "$CAPTURED.out.produced" ||
  fail "PAPERLEAN_IMPORT=check alone runs the fold comparison"

# The folds this patch added are started on another thread. The workers are shared, so the list
# starts the folds that are worth most first; these are the largest three (7.0, 5.8 and 0.8 ms per
# module on the `small128` sample).
capture env PAPERLEAN_IMPORT_TIMING=1 lean Use.lean
for ext in Lean.Meta.Grind.grindExt Lean.errorExplanationExt cbvEvalExt; do
  check_out_contains "paperlean-counter importWorker.admitted ext=$ext"
done
# Without them the import builds the same states, on the importing thread. (The timing lines are
# the only difference in the output; they are removed, as `import_state.sh` does.)
for var in PAPERLEAN_IMPORT=legacy PAPERLEAN_IMPORT_THREADS=0; do
  capture env "$var" PAPERLEAN_IMPORT_TIMING=1 lean Use.lean
  { grep -v "^paperlean-" "$CAPTURED.out.produced" || true; } | $DIFF -- "$TMP_DIR/use.legacy.out" - ||
    fail "output of the import differs with $var"
  if grep -q "paperlean-counter importWorker.admitted" "$CAPTURED.out.produced"; then
    fail "$var started an import worker"
  fi
done
