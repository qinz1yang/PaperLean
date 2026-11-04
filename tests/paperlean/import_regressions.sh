# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests the import of constants and extension entries of module data that `import_constants.lean` and
# `import_entry_routing.lean` write and then import: an axiom that a later module proves, the public and
# private views of `module` files, which module owns an IR extra name, the order in which conflicts are
# reported, an extension registered during another extension's import callback, legacy files, and
# imports of IR signatures only. PaperLean's import, its check against `importModulesCore`
# (`PAPERLEAN_IMPORT=check`) and the legacy import give the same results.

HERE=$PWD
for t in import_constants import_entry_routing; do
  for mode in "" check legacy; do
    mkdir -p "$TMP_DIR/$t-$mode"
    cd "$TMP_DIR/$t-$mode"
    capture env PAPERLEAN_IMPORT="$mode" lean --run "$HERE/$t.lean"
    $DIFF -- "$HERE/$t.expected" "$CAPTURED.out.produced" || fail "$t differs (PAPERLEAN_IMPORT=$mode)"
  done
done
