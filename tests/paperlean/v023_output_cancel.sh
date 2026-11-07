case "$(uname -s)" in
  Darwin|Linux) run python3 "$TEST_DIR/paperlean/v023_output_cancel/run.py" --lean "$(command -v lean)" --out "$TMP_DIR/output-cancel" ;;
esac
