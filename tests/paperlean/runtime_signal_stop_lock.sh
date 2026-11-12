# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# `Signal.stop` must take the event-loop lock before checking or changing the
# signal state.  The C helper first forces two concurrent stop calls through the
# unlocked state check with a preload barrier; 0.2.3 then drops the loop's
# reference twice, which the helper detects from the external's reference count.
# It then raises a one-shot signal and stops it immediately, exercising the
# callback-versus-stop race that made 0.2.3 segfault.  The preload barrier is
# Linux-specific; other platforms skip this test.
case "$(uname -s)" in
  Linux) run python3 "$TEST_DIR/paperlean/runtime_signal_stop_lock/run.py" \
    --leanc "$(command -v leanc)" --cc "${CC:-}" --out "$TMP_DIR/signal-stop-lock" ;;
esac
