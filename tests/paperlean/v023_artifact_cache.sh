# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
case "$(uname -s)" in Linux|Darwin) ;; *) return 0 ;; esac
run python3 "$TEST_DIR/paperlean/v023_artifact_interrupt.py" \
  --source-root "$(dirname "$TEST_DIR")" --work "$TMP_DIR/artifact-cache"
