# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# An allocator and publisher contend on the actual slots.lock. The pending directory must
# exist while the publisher is blocked, and both entries must retain disjoint ranges.
# Also check the two persisted process-crash states and failed publication's reservation rollback.
# The descriptor and flock gate is POSIX-only; all files belong to this test's private TMP_DIR.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN
python3 "$(dirname "$FILE")/prepare_slots.py" "$(dirname "$FILE")/prepare_slots.lean" "$TMP_DIR" ||
  fail "pack slot publication or different-key allocation failed"
