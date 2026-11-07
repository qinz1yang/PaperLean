# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
case "$(uname -s)" in Darwin|Linux) ;; *) exit 0 ;; esac
cp v023_verified_file_read.lean "$TMP_DIR/Read.lean"
cp v023_verified_file_read.py "$TMP_DIR/run.py"
cd "$TMP_DIR"
run lean Read.lean -c Read.c
run leanc -o read-verified Read.c
run python3 run.py ./read-verified
