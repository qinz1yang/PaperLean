# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# `Timer.stop` on a finished one-shot timer is a no-op: it must keep the resolved
# promise that the first `Timer.next` returned.  On 0.2.3 stop clears the promise
# unconditionally, so the next `next` creates a fresh unresolved promise and a
# waiter on it blocks forever.
case "$(uname -s)" in
  Darwin|Linux) run python3 "$TEST_DIR/paperlean/runtime_common/run_with_timeout.py" --timeout 50 -- lean --run "$TEST_DIR/paperlean/runtime_timer_stop_finished/TimerStopFinished.lean" ;;
esac
