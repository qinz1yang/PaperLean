# Tests `paperlean cache get` (`src/lake/Lake/PaperLean/Cli.lean`): it runs the cache a package
# provides, or `lake cache get` if none does, and prepares; it says what to do if downloading fails
# or if several packages provide a cache.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN
WS="$TMP_DIR/ws"
mkdir -p "$TMP_DIR/a" "$TMP_DIR/b" "$WS"
cat > "$TMP_DIR/a/lakefile.toml" <<'END'
name = "a"
defaultTargets = ["A"]
[[lean_lib]]
name = "A"
END
echo "def aValue : Nat := 1" > "$TMP_DIR/a/A.lean"
cat > "$TMP_DIR/b/lakefile.toml" <<'END'
name = "b"
defaultTargets = ["B"]
[[lean_lib]]
name = "B"
END
echo "def bValue : Nat := 2" > "$TMP_DIR/b/B.lean"
cache_exe() {
  cat >> "$TMP_DIR/$1/lakefile.toml" <<'END'
[[lean_exe]]
name = "cache"
root = "Cache"
END
  cat > "$TMP_DIR/$1/Cache.lean" <<END
def main (args : List String) : IO UInt32 := do
  if ← System.FilePath.pathExists "fail-download" then return 1
  IO.println s!"downloaded for $1: {args}"
  return 0
END
}
cd "$WS"
cat > lakefile.toml <<'END'
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "a"
path = "../a"
[[require]]
name = "b"
path = "../b"
[[lean_lib]]
name = "Root"
END
echo "import A" > Root.lean
run lake build

# Nothing to download: no package provides a cache or comes from Reservoir.
capture_exit 1 lake paperlean cache get
check_out_contains "there is nothing to download"
check_out_contains "Build the dependencies with \`lake build\`, then run \`paperlean prepare\`."
! grep -Fq "downloading failed" "$CAPTURED.out.produced" || fail "a download was reported"
[ ! -e .lake/paperlean/env.json ] || fail "prepared without a download"

# With arguments, or a package from Reservoir: Lake's artifact cache (here a registry that does not
# exist).
export RESERVOIR_API_URL="file://$TMP_DIR/no-reservoir"
capture_exit 1 lake paperlean cache get --repo test/b
check_out_contains "No package provides a cache; running \`lake cache get\`."
check_out_contains "downloading failed; if nothing can be downloaded, build the dependencies with \`lake build\`"
perl -0pi -e 's|^path = "../b"$|path = "../b"\nscope = "test"|m' lakefile.toml
rm lake-manifest.json
capture_exit 1 lake paperlean cache get
check_out_contains "No package provides a cache; running \`lake cache get\`."
check_out_contains "downloading failed"
[ ! -e .lake/paperlean/env.json ] || fail "prepared after a failed download"

# One package provides a cache: it runs, with the arguments, and then the dependencies are prepared.
cache_exe a
capture lake paperlean cache get --quick
check_out_contains "Running a's cache: lake exe a/cache get --quick"
check_out_contains "downloaded for a: [get, --quick]"
check_out_contains "Prepared"

# The cache fails.
touch fail-download
capture_exit 1 lake paperlean cache get
check_out_contains "downloading failed; if nothing can be downloaded, build the dependencies with \`lake build\`"
! grep -Fq "Prepared" "$CAPTURED.out.produced" || fail "prepared after a failed download"
rm fail-download

# Several packages provide a cache: nothing runs.
cache_exe b
capture_exit 1 lake paperlean cache get
check_out_contains "several packages provide a cache"
! grep -Fq "downloading failed" "$CAPTURED.out.produced" || fail "a download was reported"
! grep -Fq "downloaded for" "$CAPTURED.out.produced" || fail "a cache ran"
