# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
case "$(uname -s)" in Linux|Darwin) ;; *) return 0 ;; esac
unset ELAN_TOOLCHAIN LEAN_PATH LEAN_IMPORT_IMAGE LEAN_OLEAN_PACK PAPERLEAN_IMPORT PAPERLEAN_NATIVE_LIBS
python3 "$(dirname "$FILE")/private_cache.py" "$TMP_DIR" || fail "default cache permissions"
