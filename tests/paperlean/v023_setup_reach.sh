# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
source_path="${PAPERLEAN_SETUP_INDEX_SOURCE:-$(cd ../.. && pwd -P)/src/lake/Lake/PaperLean/SetupIndex.lean}"
if [ ! -f "$source_path" ]; then
  source_path="$(lean --print-prefix)/src/lean/lake/Lake/PaperLean/SetupIndex.lean"
fi
python3 v023_setup_reach.py "$source_path" "$TMP_DIR/Reach.lean"
capture lean --run "$TMP_DIR/Reach.lean"
check_out_contains "selected closures, retry, and linear edge visits passed"
