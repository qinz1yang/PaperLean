# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Lake's release-build cache (`preferReleaseBuild`) takes the existence of the package's build
# directory for a complete unpack (`Package.fetchBuildArchive`, `maybeFetchBuildCache`). An
# extraction that fails or is interrupted must therefore not leave a partial build directory: the
# archive is extracted into `build.unpack` and renamed into place once complete. Fake `git`, `curl`
# and `tar` stand in for the release download; the fake `tar` writes `one.txt`, and then fails or
# writes `two.txt`. (On rc3 and 0.2.3 the second build below reports success without running `tar`
# again, leaving `two.txt` missing.) An existing build directory is still extracted over, as before.

ROOT="$TMP_DIR/cache-unpack"
mkdir -p "$ROOT/bin" "$ROOT/proj"
cat > "$ROOT/bin/git" <<'EOF'
#!/usr/bin/env bash
case "$1" in
  describe) echo v1; exit 0;;
  rev-parse) echo 1111111111111111111111111111111111111111; exit 0;;
  *) exit 1;;
esac
EOF
cat > "$ROOT/bin/curl" <<'EOF'
#!/usr/bin/env bash
dest=""
while [[ $# -gt 0 ]]; do
  case "$1" in -o) shift; dest="$1";; esac
  shift
done
cp "${ARCHIVE_SRC:?}" "$dest"
EOF
cat > "$ROOT/bin/tar" <<'EOF'
#!/usr/bin/env bash
dir=""
while [[ $# -gt 0 ]]; do
  case "$1" in -C) shift; dir="$1"; shift;; *) shift;; esac
done
n=$(( $(cat "${FAKE_TAR_STATE:?}" 2>/dev/null || echo 0) + 1 ))
echo "$n" > "$FAKE_TAR_STATE"
mkdir -p "$dir"
echo one > "$dir/one.txt"
if [[ "${FAKE_TAR_FAIL:-0}" == 1 ]]; then
  echo "fake tar: failure after a partial extraction" >&2
  exit 1
fi
echo two > "$dir/two.txt"
EOF
chmod +x "$ROOT/bin/"*
cat > "$ROOT/proj/lakefile.toml" <<'EOF'
name = "test"
preferReleaseBuild = true
releaseRepo = "https://example.invalid/repo"
EOF
printf 'not really a tar\n' > "$ROOT/proj/source.tar.gz"
export PATH="$ROOT/bin:$PATH" ARCHIVE_SRC="$ROOT/proj/source.tar.gz" FAKE_TAR_STATE="$ROOT/tarstate"
cd "$ROOT/proj"

# A failed extraction leaves no build directory, and the next build extracts again.
export FAKE_TAR_FAIL=1
capture_fail lake build :cache
[ ! -e .lake/build ] || fail "a failed extraction left a build directory"
[ ! -e .lake/build.unpack ] || fail "a failed extraction left its staging directory"
export FAKE_TAR_FAIL=0
capture lake build :cache
[ -f .lake/build/two.txt ] || fail "the second build did not extract the archive again"
[ "$(cat "$FAKE_TAR_STATE")" = 2 ] || fail "tar did not run exactly twice"

# The staging directory of an interrupted extraction is discarded.
rm -rf .lake/build .lake/build.unpack "$FAKE_TAR_STATE"
mkdir -p .lake/build.unpack && echo stale > .lake/build.unpack/stale.txt
export FAKE_TAR_FAIL=0
capture lake build :cache
[ -f .lake/build/two.txt ] || fail "the build after an interrupted extraction did not extract"
[ ! -e .lake/build/stale.txt ] || fail "files of an interrupted extraction were kept"
[ ! -e .lake/build.unpack ] || fail "the staging directory was left behind"

# An existing build directory is extracted over (when the archive changed), as by Lake before.
rm -rf .lake/build "$FAKE_TAR_STATE" && mkdir -p .lake/build && echo keep > .lake/build/keep.txt
find .lake -name '*.trace' -delete
export FAKE_TAR_FAIL=0
capture lake build :cache
[ -f .lake/build/two.txt ] || fail "an existing build directory was not extracted over"
[ -f .lake/build/keep.txt ] || fail "files of an existing build directory were removed"

# A failed extraction over an existing build directory is not complete: the next
# build must run tar again instead of trusting the trace plus the directory.
rm -rf .lake/build .lake/build.unpack .lake/build-cache-unpack.pending "$FAKE_TAR_STATE"
mkdir -p .lake/build && echo keep > .lake/build/keep.txt
find .lake -name '*.trace' -delete
export FAKE_TAR_FAIL=1
capture_fail lake build :cache
[ -f .lake/build/keep.txt ] || fail "a failed extraction removed the old build directory"
export FAKE_TAR_FAIL=0
capture lake build :cache
[ -f .lake/build/two.txt ] || fail "the build after a failed extraction did not extract again"
[ -f .lake/build/keep.txt ] || fail "the successful retry removed files of the old build directory"
[ "$(cat "$FAKE_TAR_STATE")" = 2 ] || fail "tar did not run exactly twice for the failed-then-complete extraction"

# A dependency's partial tree that cannot be removed (a subdirectory without write permission, as an
# interrupted unpack by another user can leave). Before the dependency is built from source, both
# fallback paths (`--no-cache`, and a cache fetch that fails) must remove the tree or move it aside
# before they delete the pending marker; if neither works, the marker stays and the build fails,
# instead of building over the partial tree and forgetting it (`Lake/Build/Package.lean`,
# `discardPartialUnpack`). Run as an ordinary user: permission bits do not stop root.
WS="$ROOT/ws"
mkdir -p "$WS/dep"
cat > "$WS/lakefile.toml" <<'EOF'
name = "root"
[[require]]
name = "dep"
path = "dep"
[[lean_lib]]
name = "Root"
EOF
cat > "$WS/dep/lakefile.toml" <<'EOF'
name = "dep"
preferReleaseBuild = true
releaseRepo = "https://example.invalid/repo"
[[lean_lib]]
name = "Dep"
EOF
printf 'def dep : Nat := 1\n' > "$WS/dep/Dep.lean"
printf 'import Dep\n#eval dep\n' > "$WS/Root.lean"
release_perms() { chmod -R u+w "$WS/dep/.lake" 2>/dev/null || true; }
partial_tree() { # a pending marker and a partial build tree with an unremovable part
  release_perms
  rm -rf "$WS/dep/.lake" "$WS/.lake/build"
  mkdir -p "$WS/dep/.lake/build/locked"
  printf 'incomplete archive data\n' > "$WS/dep/.lake/build/locked/partial"
  : > "$WS/dep/.lake/build-cache-unpack.pending"
  chmod 555 "$WS/dep/.lake/build/locked"
}
cd "$WS"
export FAKE_TAR_FAIL=1   # every cache fetch of `dep` fails (the second path)
for path in nocache fetch; do
  if [ "$path" = nocache ]; then args=(--no-cache); else args=(); fi
  # The tree is moved aside: the marker goes and the build reads none of the partial files.
  partial_tree
  capture lake "${args[@]}" build Root
  [ ! -e dep/.lake/build/locked ] || fail "$path: the partial tree is still the build directory"
  [ -f dep/.lake/build.partial-1/locked/partial ] || fail "$path: the partial tree was not moved aside"
  [ ! -e dep/.lake/build-cache-unpack.pending ] || fail "$path: the marker was kept after the tree was moved aside"
  [ -n "$(find dep/.lake/build -name 'Dep.olean' 2>/dev/null)" ] || fail "$path: dep was not built from source"
  # Neither removed nor moved aside (no write permission where the tree lies): the build fails, and
  # the marker and the tree stay.
  partial_tree
  chmod 555 dep/.lake
  capture_fail lake "${args[@]}" build Root
  release_perms
  grep -q "could not be removed or moved aside" "$CAPTURED.out.produced" ||
    fail "$path: the failure does not say that the partial tree could not be removed or moved aside"
  [ -e dep/.lake/build-cache-unpack.pending ] || fail "$path: the marker was deleted although the tree stayed"
  [ -f dep/.lake/build/locked/partial ] || fail "$path: the partial tree disappeared without being moved aside"
  [ -z "$(find dep/.lake/build -name 'Dep.olean' 2>/dev/null)" ] || fail "$path: dep was built over the partial tree"
done
release_perms
true
