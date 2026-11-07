# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
cp "$TEST_DIR/paperlean/v023_setup_observation.lean" "$TMP_DIR/Observation.lean"
run lean --root="$TMP_DIR" --c="$TMP_DIR/Observation.c" "$TMP_DIR/Observation.lean"
link=(-lLake_shared -leanshared -lleanshared)
if [[ "$OSTYPE" != "cygwin" && "$OSTYPE" != "msys" ]]; then
  link+=(-Wl,-rpath,"$BUILD_DIR/lib/lean")
fi
run leanc ${LEANC_OPTS-} -O2 -o "$TMP_DIR/observation" "$TMP_DIR/Observation.c" "${link[@]}"
run "$TMP_DIR/observation"
