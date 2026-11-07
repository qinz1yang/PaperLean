# Copyright (c) 2026 PaperLean contributors. Released under the Apache 2.0 license.
src="$TEST_DIR/paperlean/v023_uv_abi.c"
run leanc ${LEANC_OPTS-} -O1 "$src" -o "$TMP_DIR/uv-abi"
run "$TMP_DIR/uv-abi"

case "$(uname -s)" in Darwin|Linux) ;; *) exit 0 ;; esac
# CMake's downloaded libuv and a system-installed libuv are both supported.
uv_args=("-I$BUILD_DIR/libuv/src/libuv/include")
if command -v pkg-config >/dev/null && pkg-config --exists libuv; then
  read -r -a system_uv_args <<< "$(pkg-config --cflags libuv)"
  uv_args+=("${system_uv_args[@]}")
fi
run ${CXX:-c++} -std=c++20 -DLEAN_MULTI_THREAD -I"$SRC_DIR" -I"$BUILD_DIR/include" -I"$BUILD_DIR" \
  "${uv_args[@]}" -c "$TEST_DIR/paperlean/v023_uv_abi_fault.cpp" -o "$TMP_DIR/uv-config-fault.o"
# leanc selects the stage's static Lean libraries and their platform-specific link options.
# The explicit object supplies the event loop, so its archive member isn't extracted a second time.
run leanc ${LEANC_OPTS-} -O1 -DUV_ABI_INJECT "$src" "$TMP_DIR/uv-config-fault.o" -o "$TMP_DIR/uv-abi-negative"
run "$TMP_DIR/uv-abi-negative"
