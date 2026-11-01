# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests `paperlean build --prepare` (`refresh`, `src/lake/Lake/PaperLean/Prepare.lean`): the files
# of the root package's modules that changed or were added since its pack was written go into a pack
# of their own, which Lean reads before the root package's pack (`find_in_packs`); that pack is not
# rewritten, every file is served from the packs, and the results equal those without packs; what
# interrupted runs left is deleted.

WS="$(cd "$TMP_DIR" && pwd -P)/ws"
mkdir -p "$TMP_DIR/dep" "$WS/Root"
cat > "$TMP_DIR/dep/lakefile.toml" <<'END'
name = "dep"
defaultTargets = ["Dep"]
[[lean_lib]]
name = "Dep"
END
echo "def depValue : Nat := 41" > "$TMP_DIR/dep/Dep.lean"
cd "$WS"
cat > lakefile.toml <<'END'
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "dep"
path = "../dep"
[[lean_lib]]
name = "Root"
END
printf 'import Root.A\nimport Root.B\n' > Root.lean
printf 'import Dep\ndef a : Nat := depValue\n' > Root/A.lean
printf 'import Root.A\ndef b : Nat := a + 1\n' > Root/B.lean
cat > Probe.lean <<'END'
import Root
import Lean.PaperLean.OLeanPack
#eval show IO Unit from do
  let (served, notServed) ← Lean.PaperLean.OLeanPack.stats
  IO.println s!"served from packs: {decide (served > 0)}, read from disk: {notServed}"
#eval b
END
# the output of Probe without prepared data, apart from the line about packs
expected() {
  capture env LEAN_OLEAN_PACK= lake env lean Probe.lean
  grep -v "served from packs" "$CAPTURED.out.produced" > "$TMP_DIR/expected.out"
}
same_as_expected() {
  grep -v "served from packs" "$CAPTURED.out.produced" | $DIFF -- "$TMP_DIR/expected.out" - ||
    fail "the output differs from the one without prepared data"
}
inode() { ls -i "$1" | awk '{print $1}'; }

# A misspelt name builds nothing.
capture_exit 1 lake paperlean build --prepare=rot
check_out_contains "did you mean the package root?"
check_out_contains "Nothing was built"
[ -e .lake/build ] && fail "a build ran"

# With nothing prepared, everything is prepared after the build.
capture lake paperlean build --prepare
check_out_contains "Nothing is prepared yet; preparing everything."
check_out_contains "of root"
BASE=$(ls .lake/paperlean/root-*/root.paperlean)
BASE_ID=$(inode "$BASE")
expected
capture env PAPERLEAN_ACCELERATE=1 lake env lean Probe.lean
check_out_contains "served from packs: true, read from disk: 0"
same_as_expected

# Nothing changed: no pack of changes.
capture lake paperlean build --prepare
check_out_contains "Nothing of root changed since its pack was written."
ls .lake/paperlean/root-*/changes-*.delta.paperlean 2>/dev/null && fail "a pack of changes without changes"

# A changed module and a new one go into the pack of changes; the root package's pack stays.
printf 'def a2 : Nat := 2\n' >> Root/A.lean
printf 'import Root.B\ndef c : Nat := b + a2\n' > Root/C.lean
printf 'import Root.C\n' >> Root.lean
printf '#eval c\n' >> Probe.lean
capture lake paperlean build --prepare
check_out_contains "modules of root that changed or were added since its pack was written"
[ "$(inode "$BASE")" = "$BASE_ID" ] || fail "the root package's pack was rewritten"
DELTA=$(ls .lake/paperlean/root-*/changes-*.delta.paperlean)
capture lake paperlean status
check_out_contains "0 of 4 modules changed since packing"
check_out_contains "the modules of root that changed since its pack was written"
capture lake paperlean build
! grep -Fq "changed since packing and are read from disk" "$CAPTURED.out.produced" ||
  fail "build reports changed modules that the pack of changes serves"
expected
capture env PAPERLEAN_ACCELERATE=1 lake env lean Probe.lean
check_out_contains "served from packs: true, read from disk: 0"
same_as_expected

# A later change replaces the pack of changes; without --prepare, status counts the changed modules.
printf 'def a3 : Nat := 3\n' >> Root/A.lean
run lake build
capture lake paperlean status
check_out_matches "[1-4] of 4 modules changed since packing"
capture lake paperlean build --prepare
[ -e "$DELTA" ] && fail "the previous pack of changes is still there"
ls .lake/paperlean/root-*/changes-*.delta.paperlean > /dev/null || fail "no pack of changes"
[ "$(inode "$BASE")" = "$BASE_ID" ] || fail "the root package's pack was rewritten"
expected
capture env PAPERLEAN_ACCELERATE=1 lake env lean Probe.lean
check_out_contains "served from packs: true, read from disk: 0"
same_as_expected

# A failure after the pack of changes was written (here: env.json cannot be written) leaves the data
# as it was, without that pack.
DELTAS=$(ls .lake/paperlean/root-*/changes-*.delta.paperlean)
cp .lake/paperlean/env.json "$TMP_DIR/env.before"
printf 'def a4 : Nat := 4\n' >> Root/A.lean
chmod a-w .lake/paperlean
capture_exit 1 lake paperlean build --prepare
chmod u+w .lake/paperlean
[ "$(ls .lake/paperlean/root-*/changes-*.delta.paperlean)" = "$DELTAS" ] || fail "a failed refresh left a pack of changes"
cmp -s .lake/paperlean/env.json "$TMP_DIR/env.before" || fail "a failed refresh changed env.json"
capture lake paperlean build --prepare
expected
capture env PAPERLEAN_ACCELERATE=1 lake env lean Probe.lean
check_out_contains "served from packs: true, read from disk: 0"
same_as_expected
# The packs of changes that interrupted runs left (here made by hand) and their temporary files are
# deleted by the next run.
RDIR=$(dirname "$BASE")
touch "$RDIR/changes-1.delta.paperlean" "$RDIR/changes-2.delta.paperlean.tmp.99999999"
capture lake paperlean build --prepare
[ ! -e "$RDIR/changes-1.delta.paperlean" ] && [ ! -e "$RDIR/changes-2.delta.paperlean.tmp.99999999" ] ||
  fail "build --prepare kept what interrupted runs left: $(ls "$RDIR")"
ls "$RDIR"/changes-*.delta.paperlean > /dev/null || fail "build --prepare deleted its pack of changes"

# Preparing the dependencies again keeps the root package's packs.
capture lake paperlean build --prepare=dep
check_out_contains "Preparing dep again"
capture lake paperlean status
check_out_contains "0 of 4 modules changed since packing"
capture env PAPERLEAN_ACCELERATE=1 lake env lean Probe.lean
check_out_contains "served from packs: true, read from disk: 0"
same_as_expected
