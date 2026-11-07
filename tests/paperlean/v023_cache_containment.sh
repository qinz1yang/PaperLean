# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
cat > "$TMP_DIR/CacheProbe.lean" <<'LEAN'
import Lake.PaperLean.Cache
open System Lake.PaperLean
def main (args : List String) : IO Unit := do
  let [op, dir, value] := args | throw <| IO.userError "expected operation, directory and argument"
  let dir : FilePath := dir
  match op with
  | "collect" => discard <| Cache.collect dir value.toNat!
  | "touch" => Cache.touch dir #[value]
  | "user" => Cache.addUser dir value
  | "key" => IO.println (Cache.key #[value])
  | "dir" => IO.println (Cache.buildDir dir)
  | _ => throw <| IO.userError "unknown operation"
LEAN
run lean --root="$TMP_DIR" --c="$TMP_DIR/cache.c" "$TMP_DIR/CacheProbe.lean"
link=(-lLake_shared -leanshared -lleanshared)
if [[ "$OSTYPE" != "cygwin" && "$OSTYPE" != "msys" ]]; then
  link+=(-Wl,-rpath,"$BUILD_DIR/lib/lean")
fi
run leanc ${LEANC_OPTS-} -O2 -o "$TMP_DIR/cache_probe" "$TMP_DIR/cache.c" "${link[@]}"
run python3 "$TEST_DIR/paperlean/v023_cache_containment.py" "$TMP_DIR/cache_probe" "$TMP_DIR/cases"
