# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# A cache hook restores the heartbeat counter in a `finally`, also when the lookup throws. The
# hook here (`TCCache.getInstancesUnify`) throws `isDefEqStuck` from `getUnifyRootKey`; the cache's
# work must not remain counted, or a caught and retried search in one command is overcharged.
run lean "$TEST_DIR/paperlean/tccache_heartbeats.lean"
