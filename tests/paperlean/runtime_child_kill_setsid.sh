# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# `Child.kill` must terminate a child spawned with `setsid := true` even when the
# child has not called setsid() yet.  Before the fix the parent's killpg(pid, ...)
# failed with ESRCH, so the child survived the kill.  A preload library delays the
# child's setsid() and reports that it has been reached, making the window
# deterministic rather than scheduling-dependent.
case "$(uname -s)" in
  Linux) run python3 "$TEST_DIR/paperlean/runtime_child_kill_setsid/run.py" \
    --lean "$(command -v lean)" --cc "${CC:-}" --out "$TMP_DIR/child-kill-setsid" ;;
esac
