cp "$TEST_DIR/paperlean/v023_csimp_native.lean" "$TMP_DIR/Choices.lean"
cd "$TMP_DIR"
run lean -c Choices.c Choices.lean
run leanc -O1 -o Choices Choices.c
run ./Choices
