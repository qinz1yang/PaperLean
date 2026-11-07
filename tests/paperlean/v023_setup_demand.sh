# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
cp v023_setup_demand.lean v023_setup_demand.py "$TMP_DIR/"
run lean --root="$TMP_DIR" --c="$TMP_DIR/setup_demand.c" "$TMP_DIR/v023_setup_demand.lean"
link=(-leanshared -lleanshared)
if [[ "$OSTYPE" != "cygwin" && "$OSTYPE" != "msys" ]]; then
  link+=(-Wl,-rpath,"$BUILD_DIR/lib/lean")
fi
run leanc ${LEANC_OPTS-} -O2 -o "$TMP_DIR/setup_demand" "$TMP_DIR/setup_demand.c" "${link[@]}"
run python3 "$TMP_DIR/v023_setup_demand.py" "$TMP_DIR/setup_demand" "$TMP_DIR/v023-demand"
