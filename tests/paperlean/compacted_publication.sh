# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# The compacted region writer also serves the ordinary lean -o frontend.
case "$(uname -s)" in Darwin|Linux) ;; *) return 0 ;; esac
unset LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS ELAN_TOOLCHAIN
python3 "$(dirname "$FILE")/compacted_publication.py" "$TMP_DIR" ||
  fail "compacted region publication was destructive or incomplete"
