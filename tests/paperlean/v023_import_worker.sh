# Isolate the temporary invalid pthread stack size in a new native process.
case "$(uname -s)" in
  Darwin|Linux) ;;
  *) exit 0 ;;
esac
cd "$TMP_DIR"
cp "$TEST_DIR/paperlean/v023_import_worker/Unavailable.lean" .
run lean -c Unavailable.c Unavailable.lean
run leanc ${LEANC_OPTS-} -o unavailable Unavailable.c
capture env PAPERLEAN_IMPORT_THREADS=1 ./unavailable
check_out_contains "recovered"
