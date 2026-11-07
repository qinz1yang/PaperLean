case "$(uname -s)" in
  Darwin|Linux) run python3 "$TEST_DIR/paperlean/v023_posix_spawn/run.py" --lean "$(command -v lean)" --leanc "$(command -v leanc)" --work "$TMP_DIR/posix-spawn" ;;
esac
