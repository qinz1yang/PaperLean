# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
NAME="$1"
FILE="$(realpath "$1")"
# The tests start without the variables that change what PaperLean does, whatever the caller set.
unset $(compgen -e | grep '^PAPERLEAN_' || true) LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE ELAN_TOOLCHAIN
# Apple's Python launcher exports its own SDK and search paths to child shells.
# Test the default native driver; individual tests provide explicit overrides when required.
unset CPATH LIBRARY_PATH SDKROOT
# Each test has a cache of prepared data of its own, not the user's.
export PAPERLEAN_CACHE_DIR="$(cd "$TMP_DIR" && pwd -P)/paperlean-cache"
source "$1"
