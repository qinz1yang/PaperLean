# Tests the olean packs that a build writes for its later `lean` processes
# (`src/lake/Lake/PaperLean/BuildData.lean`), which only the Lake of `paperlean` commands writes
# (`PAPERLEAN_ACCELERATE`), never plain `lake`: a build without prepared data that packs (here forced,
# a few modules per pack) packs the modules it compiles and writes the pack of the toolchain's library
# into the cache directory once; the modules compile to the same files and traces as without packs,
# without warnings; every pack serves the files it holds, with the same results; the build removes its packs
# at the end, the next build those of an earlier one that kept them, and the toolchain packs beyond
# the two newest others that no build uses; a small build, a build with prepared data and one with
# `PAPERLEAN_BUILD_PACKS=0` write no packs.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN PAPERLEAN_DATA PAPERLEAN_BUILD_PACKS PAPERLEAN_BUILD_PACK_BATCH PAPERLEAN_BUILD_PACKS_KEEP
unset PAPERLEAN_CACHE_DIR
export XDG_CACHE_HOME="$(cd "$TMP_DIR" && pwd -P)/cache"
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
printf 'import Root.D\nimport Root.Sub.E\n' > Root.lean
mkdir -p Root/Sub
printf 'import Root.C\ndef e : Nat := c + 1\n' > Root/Sub/E.lean
printf 'import Dep\ndef a : Nat := depValue\n' > Root/A.lean
printf 'import Root.A\ntheorem ta : a = 41 := rfl\ndef b : Nat := a + 1\n' > Root/B.lean
printf 'import Root.B\ninstance : Inhabited (Fin (b + 1)) := ⟨0⟩\ndef c : Nat := b + 1\n' > Root/C.lean
printf 'import Root.C\nimport Lean\nopen Lean in\n#eval show MetaM Unit from do logInfo m!"{c}"\n' > Root/D.lean
cat > Probe.lean <<'END'
import Root
import Lean.PaperLean.OLeanPack
#eval show IO Unit from do
  let (served, _) ← Lean.PaperLean.OLeanPack.stats
  IO.println s!"served from packs: {decide (served > 0)}"
#eval c
END
# the files that a build writes, with the traces, whose logs show Lake's commands
outputs() { (cd "$TMP_DIR" && find ws/.lake/build dep/.lake/build -name '*.olean*' -o -name '*.ir*' -o -name '*.trace' | sort); }
clean() { rm -rf .lake/build ../dep/.lake/build; }
packdirs() { ls -d .lake/paperlean/build/*/ 2>/dev/null; }

# Without packs: the reference files.
clean
run env PAPERLEAN_BUILD_PACKS=0 lake build
[ -z "$(packdirs)" ] || fail "PAPERLEAN_BUILD_PACKS=0 wrote packs: $(packdirs)"
for f in $(outputs); do mkdir -p "$TMP_DIR/ref/$(dirname "$f")"; cp "$TMP_DIR/$f" "$TMP_DIR/ref/$f"; done

# Plain `lake` does not pack, even if forced to.
clean
run env PAPERLEAN_BUILD_PACKS=1 lake build
[ -z "$(packdirs)" ] || fail "plain lake wrote packs: $(packdirs)"
[ ! -e "$XDG_CACHE_HOME/paperlean" ] || fail "plain lake packed the toolchain's library"
export PAPERLEAN_ACCELERATE=1

# A small build does not pack.
clean
run lake build
[ -z "$(packdirs)" ] || fail "a small build wrote packs: $(packdirs)"
[ ! -e "$XDG_CACHE_HOME/paperlean" ] || fail "a small build packed the toolchain's library"

# Packing (forced), three modules per pack (of different directories), packs kept: the same files.
clean
capture env PAPERLEAN_BUILD_PACKS=1 PAPERLEAN_BUILD_PACK_BATCH=3 PAPERLEAN_BUILD_PACKS_KEEP=1 lake build
! grep -i "warning" "$CAPTURED.out.produced" || fail "the build with packs printed warnings"
for f in $(outputs); do
  cmp -s "$TMP_DIR/$f" "$TMP_DIR/ref/$f" || fail "$f differs from the build without packs"
done
dir=$(packdirs)
[ "$(echo "$dir" | wc -w)" = 1 ] || fail "expected one directory of packs: $dir"
[ "$(ls "$dir"/pack-*.paperlean 2>/dev/null | wc -l)" -ge 1 ] || fail "no module was packed: $(ls "$dir")"
tc="$XDG_CACHE_HOME/paperlean/toolchain-packs"
lib=$(ls "$tc"/lib-*.paperlean 2>/dev/null)
[ "$(echo "$lib" | wc -w)" = 1 ] || fail "expected one pack of the toolchain's library: $(ls "$tc")"
[ "$(ls "$tc" | wc -l)" = 1 ] || fail "files left in the cache directory: $(ls "$tc")"

# Every pack serves its files, with the same results as without packs.
capture lake env lean Probe.lean
grep -v "served from packs" "$CAPTURED.out.produced" > "$TMP_DIR/expected.out"
packs="$lib:$(ls "$dir"/pack-*.paperlean | tr '\n' ':')"
capture env LEAN_OLEAN_PACK="$packs" lake env lean Probe.lean
check_out_contains "served from packs: true"
grep -v "served from packs" "$CAPTURED.out.produced" | $DIFF -- "$TMP_DIR/expected.out" - ||
  fail "the output with the packs differs"

# The next build removes the packs of the earlier one (another process), and its own at the end;
# the toolchain's pack is used again; of four packs of other toolchains, the two newest and the one in
# use (locked) are kept.
lib_inode=$(ls -i "$lib" | awk '{print $1}')
for i in 1 2 3 4; do
  echo old > "$tc/lib-0-old$i-x.paperlean"; touch -d "$i days ago" "$tc/lib-0-old$i-x.paperlean"
done
exec 9< "$tc/lib-0-old4-x.paperlean"
flock -s 9
clean
run env PAPERLEAN_BUILD_PACKS=1 PAPERLEAN_BUILD_PACK_BATCH=1 lake build
exec 9<&-
[ ! -e "$dir" ] || fail "the packs of the earlier build were not removed"
[ -z "$(packdirs)" ] || fail "the build did not remove its packs: $(packdirs)"
[ "$(ls -i "$lib" | awk '{print $1}')" = "$lib_inode" ] || fail "the toolchain's pack was written again"
for i in 1 2 4; do
  [ -f "$tc/lib-0-old$i-x.paperlean" ] || fail "the toolchain pack old$i was removed: $(ls "$tc")"
done
[ ! -e "$tc/lib-0-old3-x.paperlean" ] || fail "the toolchain pack old3 was kept: $(ls "$tc")"

# With prepared data, no packs are written.
clean
run lake build
run lake paperlean build --prepare=root
touch Root/D.lean
run env PAPERLEAN_BUILD_PACKS=1 PAPERLEAN_BUILD_PACKS_KEEP=1 lake build
[ -z "$(packdirs)" ] || fail "a build with prepared data wrote packs: $(packdirs)"
