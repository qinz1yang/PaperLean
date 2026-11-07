# A prepare evaluation must certify the module it read. Exercise the real Mac loader
# and a file replacement confined to the open syscall, leaving the original inode intact.
[ "$(uname -s)" = Darwin ] || exit 0
run python3 "$TEST_DIR/paperlean/v023_native_eval_aba.py" "$TMP_DIR"
