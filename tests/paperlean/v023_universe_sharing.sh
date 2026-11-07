# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
# Seventy-two nodes would take 2^72 visits when treated as a tree.
run env PAPERLEAN_REUSE=1 PAPERLEAN_REUSE_MIN_HEARTBEATS=0 python3 - \
  "$TEST_DIR/paperlean/v023_universe_sharing.lean" <<'PY'
import subprocess
import sys
subprocess.run(["lean", sys.argv[1]], check=True, timeout=30)
PY
