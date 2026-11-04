# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# A different-key allocator runs while a publisher is paused inside its slot metadata read. The
# pending directory must still exist then, and both published entries must retain disjoint ranges.
# Also check the two persisted process-crash states and failed publication's reservation rollback.
# The FIFO and flock gate is POSIX-only; all files belong to this test's private TMP_DIR.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN
python3 "$(dirname "$FILE")/prepare_slots.py" "$(dirname "$FILE")/prepare_slots.lean" "$TMP_DIR" ||
  fail "pack slot publication or different-key allocation failed"
