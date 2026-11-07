# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
case "$(uname -s)" in Linux|Darwin) ;; *) return 0 ;; esac
unset ELAN_TOOLCHAIN LEAN_PATH LEAN_IMPORT_IMAGE LEAN_OLEAN_PACK PAPERLEAN_IMPORT PAPERLEAN_NATIVE_LIBS
python3 "$(dirname "$FILE")/pack_regular.py" "$TMP_DIR" || fail "pack special input or lock blocked"
