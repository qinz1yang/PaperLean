# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
mkdir -p "$TMP_DIR/publication/inputs"
for leaf in A B; do
  echo "def value$leaf : Nat := 100" >"$TMP_DIR/publication/inputs/$leaf.lean"
  run lean --root="$TMP_DIR/publication/inputs" -o "$TMP_DIR/publication/inputs/$leaf.olean" \
    "$TMP_DIR/publication/inputs/$leaf.lean"
done
run python3 "$TEST_DIR/paperlean/v023_pack_publication.py" "$TMP_DIR/publication" \
  "$TEST_DIR/paperlean/v023_pack_publication.lean"
