# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Decoding EINTR or ENOENT without a file name must not dereference the null name.
# The public Handle.lock path passes no file name when flock(2) is interrupted by a
# signal whose handler does not set SA_RESTART; DNS/TCP/UDP callbacks reach the same
# decoder with a null name.  0.2.3 crashes in both branches.
case "$(uname -s)" in
  Darwin|Linux) run python3 "$TEST_DIR/paperlean/runtime_decode_error_no_name/run.py" \
    --leanc "$(command -v leanc)" --out "$TMP_DIR/decode-no-name" ;;
esac
