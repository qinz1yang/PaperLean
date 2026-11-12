# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# `IO.FS.realPath` must report the errno and IO.Error class produced by
# realpath(3), not a hardcoded ENOENT.  ENOTDIR on a path through a regular file
# and EACCES on a directory without search permission are both checked; 0.2.3
# reports "no such file or directory" with code 2 for both.
case "$(uname -s)" in
  Darwin|Linux) run python3 "$TEST_DIR/paperlean/runtime_realpath_errno/run.py" \
    --lean "$(command -v lean)" --out "$TMP_DIR/realpath-errno" ;;
esac
