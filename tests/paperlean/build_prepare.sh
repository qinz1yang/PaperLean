# Tests `paperlean build --prepare` (`refresh`, `src/lake/Lake/PaperLean/Prepare.lean`): the files
# of the root package's modules that changed or were added since its pack was written go into a pack
# of their own, which Lean reads before the root package's pack (`find_in_packs`); that pack is not
# rewritten, every file is served from the packs, and the results equal those without packs.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN
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

# Preparing the dependencies again keeps the root package's packs.
capture lake paperlean build --prepare=dep
check_out_contains "Preparing dep again"
capture lake paperlean status
check_out_contains "0 of 4 modules changed since packing"
capture env PAPERLEAN_ACCELERATE=1 lake env lean Probe.lean
check_out_contains "served from packs: true, read from disk: 0"
same_as_expected
