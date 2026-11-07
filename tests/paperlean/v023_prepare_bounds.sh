# A bounded preparation must reach genuine safe and unsafe verdicts, while an import that
# forgoes speculation must compute the same states through its normal synchronous path.
case "$(uname -s)" in
    Darwin|Linux) ;;
    *) exit 0 ;;
esac
run python3 "$TEST_DIR/paperlean/v023_prepare_bounds.py" "$TMP_DIR"
