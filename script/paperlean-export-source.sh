#!/usr/bin/env bash
# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Exports <commit> of this repository into the new directory <dir> as the source tree of a release
# build (`CHECK_OLEAN_VERSION=ON`): its `.git` has only a `HEAD` naming the upstream release commit
# (`LEAN_UPSTREAM_GITHASH` of src/CMakeLists.txt), from which the bootstrap compiler
# takes the githash that it writes into the headers of the library's `.olean` files, as when upstream
# builds its release; `PAPERLEAN_COMMIT` names <commit>, PaperLean's build.
#   script/paperlean-export-source.sh <commit> <dir>
set -euo pipefail
[ $# = 2 ] || { echo "usage: $0 <commit> <dir>" >&2; exit 1; }
COMMIT=$1 DIR=$2
REPO=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
[ ! -e "$DIR" ] || { echo "$0: $DIR exists" >&2; exit 1; }
SHA=$(git -C "$REPO" rev-parse --verify "$COMMIT^{commit}")
UPSTREAM=$(git -C "$REPO" show "$SHA:src/CMakeLists.txt" |
  sed -n 's/^set(LEAN_UPSTREAM_GITHASH "\([0-9a-f]\{40\}\)".*/\1/p')
[ -n "$UPSTREAM" ] || { echo "$0: no LEAN_UPSTREAM_GITHASH in src/CMakeLists.txt of $SHA" >&2; exit 1; }
mkdir -p "$DIR"
git -C "$REPO" archive "$SHA" | tar -x -C "$DIR"
mkdir "$DIR/.git"
echo "$UPSTREAM" > "$DIR/.git/HEAD"
echo "$SHA" > "$DIR/PAPERLEAN_COMMIT"
echo "exported $SHA with the githash $UPSTREAM"
