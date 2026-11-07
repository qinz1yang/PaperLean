# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
cd "$TMP_DIR"
printf 'def bridgeFixture : Nat := 7\n@[noinline] def bridgeAdd (n : Nat) := n+1\n' > Generated.lean
run lean --c=Generated.c Generated.lean
# No libLake_shared preload or native runner: these are interpreted users of the installed toolchain.
run env PAPERLEAN_ACCELERATE=1 PAPERLEAN_SOURCE_INPUT_CACHE=1 PAPERLEAN_CACHE_DIR="$TMP_DIR/cache" \
  lean --run "$TEST_DIR/paperlean/v023_lake_ffi.lean"
