# Copyright (c) 2026 PaperLean contributors. Released under Apache 2.0.
case "$(uname -s)" in Darwin|Linux) ;; *) exit 0 ;; esac
run ${CXX:-c++} -std=c++20 -pthread -c "$TEST_DIR/paperlean/v023_uv_first_use.cpp" -o "$TMP_DIR/first.o"
run leanc ${LEANC_OPTS-} -o "$TMP_DIR/first" "$TMP_DIR/first.o"
run "$TMP_DIR/first"
