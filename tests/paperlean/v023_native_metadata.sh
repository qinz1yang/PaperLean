# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
cp v023_native_cache.py "$TMP_DIR/"
run python3 "$TMP_DIR/v023_native_cache.py" metadata "$TMP_DIR/v023-metadata"
run python3 "$TMP_DIR/v023_native_cache.py" retained-metadata "$TMP_DIR/v023-retained-metadata"
