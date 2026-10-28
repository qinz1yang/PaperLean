# Tests `paperlean update` (`src/lake/Lake/PaperLean/Update.lean`): it predicts the toolchain an
# update leads to before changing anything (for Git and Reservoir dependencies), updates if a PaperLean
# release supports the result, keeping the project on official Lean (moving to the official toolchain
# of a new Lean version), downloads and prepares again, changes nothing otherwise, and restores the
# previous state if `lake update` fails or does something else.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN
export ELAN_HOME="$TMP_DIR/elan"
mkdir -p "$ELAN_HOME/toolchains"
export GIT_AUTHOR_NAME=test GIT_AUTHOR_EMAIL=test@example.com GIT_COMMITTER_NAME=test GIT_COMMITTER_EMAIL=test@example.com
capture lake paperlean --version
LEANVER=$(sed -n 's/.*-lean//p' "$CAPTURED.out.produced")
[ -n "$LEANVER" ] || fail "no Lean version in the PaperLean version"

# A dependency with a cache.
DEP="$TMP_DIR/deprepo"
mkdir -p "$DEP"
cd "$DEP"
git init -q -b main
cat > lakefile.toml <<'END'
name = "dep"
defaultTargets = ["Dep"]
[[lean_lib]]
name = "Dep"
[[lean_exe]]
name = "cache"
root = "DepCache"
END
echo "def depValue : Nat := 1" > Dep.lean
echo 'def main (args : List String) : IO Unit := IO.println s!"dep cache: {args}"' > DepCache.lean
echo "leanprover/lean4:v$LEANVER" > lean-toolchain
git add -A && git commit -q -m one

WS="$TMP_DIR/ws"
mkdir -p "$WS"
cd "$WS"
cat > lakefile.toml <<END
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "dep"
git = "file://$DEP"
rev = "main"
[[lean_lib]]
name = "Root"
END
echo "import Dep" > Root.lean
# the project keeps Lean's own toolchain; this build's Lake runs `paperlean` as the front end would
TC=$(dirname "$(dirname "$(command -v lake)")")
OFFICIAL="leanprover/lean4:v$LEANVER"
echo "$OFFICIAL" > lean-toolchain
run lake update
run lake build

# A new commit for the same Lean: updated, downloaded and prepared again.
(cd "$DEP" && echo "def depValue2 : Nat := 2" >> Dep.lean && git commit -q -am two)
REV2=$(git -C "$DEP" rev-parse HEAD)
capture lake paperlean update
check_out_contains "Working out what an update would do"
check_out_contains "Running dep's cache: lake exe dep/cache get"
check_out_contains "dep cache: [get]"
check_out_contains "Prepared"
[ "$(git -C .lake/packages/dep rev-parse HEAD)" = "$REV2" ] || fail "the dependency did not move to the new commit"
grep -q "$REV2" lake-manifest.json || fail "the manifest does not record the new commit"
[ "$(cat lean-toolchain)" = "$OFFICIAL" ] || fail "the toolchain changed"

# A commit for a Lean that no PaperLean supports: nothing changes.
cp lake-manifest.json "$TMP_DIR/manifest.before"
(cd "$DEP" && echo "leanprover/lean4:v4.99.0" > lean-toolchain && git commit -q -am three)
REV3=$(git -C "$DEP" rev-parse HEAD)
unchanged() {
  [ "$(git -C .lake/packages/dep rev-parse HEAD)" = "$REV2" ] || fail "the dependency moved"
  cmp lake-manifest.json "$TMP_DIR/manifest.before" || fail "the manifest changed"
  [ "$(cat lean-toolchain)" = "$1" ] || fail "the toolchain changed"
}
capture_exit 1 lake paperlean update
check_out_contains "the update needs Lean 4.99.0, and there is no PaperLean release for it"
check_out_contains "Nothing was changed"
check_out_contains "With \`lake update\`, the project updates with official Lean 4.99.0"
unchanged "$OFFICIAL"
# a misspelt name changes nothing either
capture_exit 1 lake paperlean update dpe
check_out_contains "did you mean the package dep?"
unchanged "$OFFICIAL"

# Incomparable Lean versions: nothing changes.
(cd "$DEP" && echo "leanprover/lean4:nightly-2026-01-01" > lean-toolchain && git commit -q -am four)
capture_exit 1 lake paperlean update
check_out_contains "the dependencies would need different Lean versions"
check_out_contains "dep needs leanprover/lean4:nightly-2026-01-01"
unchanged "$OFFICIAL"
# a dependency whose manifest fixes an older toolchain
(cd "$DEP" && git reset -q --hard "$REV3" && echo "leanprover/lean4:v4.0.0" > lean-toolchain &&
  echo '{"version": "1.2.0", "name": "dep", "packages": [], "fixedToolchain": true}' > lake-manifest.json &&
  git add -A && git commit -q -m fixed)
capture_exit 1 lake paperlean update
check_out_contains "the root package needs $LEANVER, dep needs 4.0.0"
unchanged "$OFFICIAL"
(cd "$DEP" && git reset -q --hard "$REV3")

# A PaperLean release for the new Lean (the newest of the installed toolchains of the origin of the
# running one, which `ELAN_TOOLCHAIN` names as the front end sets it): the project moves to official
# Lean 4.99.0 and is told which PaperLean to install.
export ELAN_TOOLCHAIN="local/test/paperlean:v0.1.0-lean$LEANVER"
for tag in v0.1.5-lean4.99.0 v0.2.0-lean4.99.0 v0.3.0-lean4.98.0; do
  mkdir -p "$ELAN_HOME/toolchains/local--test--paperlean---$tag"
done
# `lake update` failing or doing something else than predicted: the previous state comes back.
mkdir -p "$TMP_DIR/fakebin"
printf '#!/bin/sh\nexit 1\n' > "$TMP_DIR/fakebin/lake"
chmod +x "$TMP_DIR/fakebin/lake"
PATH="$TMP_DIR/fakebin:$PATH" capture_exit 1 "$TC/bin/lake" paperlean update
check_out_contains "The toolchain changes to leanprover/lean4:v4.99.0"
check_out_contains "\`lake update\` failed; the previous state is restored"
unchanged "$OFFICIAL"
printf '#!/bin/sh\nexit 0\n' > "$TMP_DIR/fakebin/lake"
PATH="$TMP_DIR/fakebin:$PATH" capture_exit 1 "$TC/bin/lake" paperlean update
check_out_contains "dep moved to $REV2, not to the predicted $REV3; the previous state is restored"
unchanged "$OFFICIAL"
capture lake paperlean update
check_out_contains "The toolchain changes to leanprover/lean4:v4.99.0"
check_out_contains "elan toolchain install local/test/paperlean:v0.2.0-lean4.99.0"
check_out_contains "dep cache: [get]"
check_out_contains "Prepared"
[ "$(git -C .lake/packages/dep rev-parse HEAD)" = "$REV3" ] || fail "the dependency did not move"
[ "$(cat lean-toolchain)" = "leanprover/lean4:v4.99.0" ] || fail "the toolchain is not official Lean 4.99.0"
unset ELAN_TOOLCHAIN

# A Reservoir dependency (a local registry): its revision comes from Reservoir's data.
RES="$TMP_DIR/reservoir"
mkdir -p "$RES/packages/test"
reservoir() {
  printf '{"data": {"name": "dep", "fullName": "test/dep", "sources": [%s]}}\n' "$1" > "$RES/packages/test/dep"
}
reservoir "{\"gitUrl\": \"file://$DEP\", \"defaultBranch\": \"main\"}"
export RESERVOIR_API_URL="file://$RES"
WSR="$TMP_DIR/wsr"
mkdir -p "$WSR"
cd "$WSR"
cat > lakefile.toml <<'END'
name = "rootr"
[[require]]
name = "dep"
scope = "test"
END
echo "$TC" > lean-toolchain
run lake update
[ "$(git -C .lake/packages/dep rev-parse HEAD)" = "$(git -C "$DEP" rev-parse HEAD)" ] || fail "Reservoir's dependency is not at main"
cp lake-manifest.json "$TMP_DIR/manifest.r"
capture_exit 1 lake paperlean update
check_out_contains "the update needs Lean 4.99.0, and there is no PaperLean release for it"
reservoir ""
capture_exit 1 lake paperlean update
check_out_contains "Reservoir has no Git source for test/dep"
rm "$RES/packages/test/dep"
capture_exit 1 lake paperlean update
check_out_contains "cannot look up test/dep on Reservoir"
# a version range needs Reservoir's version list, which this registry lacks
reservoir "{\"gitUrl\": \"file://$DEP\", \"defaultBranch\": \"main\"}"
echo 'version = "=1.0.0"' >> lakefile.toml
capture_exit 1 lake paperlean update
check_out_contains "cannot look up the versions of test/dep on Reservoir"
cmp lake-manifest.json "$TMP_DIR/manifest.r" || fail "the manifest changed"
[ "$(cat lean-toolchain)" = "$TC" ] || fail "the toolchain changed"
