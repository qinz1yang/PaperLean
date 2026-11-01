# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
NAME="$1"
FILE="$(realpath "$1")"
# The tests start without the variables that change what PaperLean does, whatever the caller set.
unset $(compgen -e | grep '^PAPERLEAN_' || true) LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE ELAN_TOOLCHAIN
source "$1"
