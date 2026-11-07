# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
cp "$TEST_DIR/paperlean/v023_setup_linked.lean" "$TMP_DIR/"
run lean --root="$TMP_DIR" --c="$TMP_DIR/linked.c" "$TMP_DIR/v023_setup_linked.lean"
link=(-leanshared -lleanshared)
if [[ "$OSTYPE" != "cygwin" && "$OSTYPE" != "msys" ]]; then
  link+=(-Wl,-rpath,"$BUILD_DIR/lib/lean")
fi
run leanc ${LEANC_OPTS-} -O2 -o "$TMP_DIR/linked" "$TMP_DIR/linked.c" "${link[@]}"
run "$TMP_DIR/linked" "$TMP_DIR/linked-data"
