# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# `UDP.Socket.cancelRecv` must release the reference that `recv`/`waitReadable`
# handed to the event loop.  Without it the socket external is never finalized,
# its uv_udp_t handle is never closed, and each cancelRecv leaks one descriptor.
# 0.2.3 leaks one descriptor per cycle; the fixed runtime stays within the event
# loop's own fixed descriptor set.
case "$(uname -s)" in
  Darwin|Linux) run python3 "$TEST_DIR/paperlean/runtime_common/run_with_timeout.py" --timeout 50 -- lean --run "$TEST_DIR/paperlean/runtime_udp_cancel_recv/UdpCancelRecv.lean" ;;
esac
