# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests the olean packs that a build writes for its later `lean` processes
# (`src/lake/Lake/PaperLean/BuildData.lean`), which only the Lake of `paperlean` commands writes
# (`PAPERLEAN_ACCELERATE`), never plain `lake`: a build without prepared data that packs (here forced,
# a few modules per pack) packs the modules it compiles and writes the pack of the toolchain's library
# into the cache directory once; the modules compile to the same files and traces as without packs,
# without warnings; every pack serves the files it holds, with the same results; the build removes its packs
# at the end, the next build those of an earlier one that kept them, and the toolchain packs beyond
# the two newest others that no build uses; without the disk space for it, the toolchain's pack is not
# written; a small build, a build with prepared data and one with `PAPERLEAN_BUILD_PACKS=0` write no
# packs; the packs of an interrupted build are removed by the next `paperlean build` or `prepare`.

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
  IO.println s!"served from packs: {served}"
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
[ ! -e "$PAPERLEAN_CACHE_DIR" ] || fail "plain lake packed the toolchain's library"
export PAPERLEAN_ACCELERATE=1

# A small build does not pack.
clean
run lake build
[ -z "$(packdirs)" ] || fail "a small build wrote packs: $(packdirs)"
[ ! -e "$PAPERLEAN_CACHE_DIR/toolchain-packs" ] || fail "a small build packed the toolchain's library"

# `PAPERLEAN_BUILD_PACKS=0` packs nothing in a build large enough to pack, which does without it.
mkdir "$TMP_DIR/many"
pushd "$TMP_DIR/many" > /dev/null
printf 'name = "many"\ndefaultTargets = ["Many"]\n[[lean_lib]]\nname = "Many"\n' > lakefile.toml
cp ../ws/lean-toolchain . 2>/dev/null || true
mkdir Many
for i in $(seq 1 33); do echo "def m$i : Nat := $i" > Many/M$i.lean; echo "import Many.M$i" >> Many.lean; done
run env PAPERLEAN_BUILD_PACKS=0 PAPERLEAN_BUILD_PACK_BATCH=3 PAPERLEAN_BUILD_PACKS_KEEP=1 lake build
[ -z "$(packdirs)" ] || fail "PAPERLEAN_BUILD_PACKS=0 wrote packs: $(packdirs)"
[ ! -e "$PAPERLEAN_CACHE_DIR/toolchain-packs" ] || fail "PAPERLEAN_BUILD_PACKS=0 packed the toolchain's library"
rm -rf .lake/build
run env PAPERLEAN_BUILD_PACK_BATCH=3 PAPERLEAN_BUILD_PACKS_KEEP=1 lake build
[ -n "$(packdirs)" ] || fail "a build of 34 modules wrote no packs"
popd > /dev/null
rm -rf "$PAPERLEAN_CACHE_DIR"

# Packing (forced), three modules per pack (of different directories), packs kept: the same files.
clean
capture env PAPERLEAN_BUILD_PACKS=1 PAPERLEAN_BUILD_PACK_BATCH=3 PAPERLEAN_BUILD_PACKS_KEEP=1 lake build
! grep -i "warning" "$CAPTURED.out.produced" || fail "the build with packs printed warnings"
for f in $(outputs); do
  cmp -s "$TMP_DIR/$f" "$TMP_DIR/ref/$f" || fail "$f differs from the build without packs"
done
dir=$(packdirs)
[ "$(echo "$dir" | wc -w | tr -d ' ')" = 1 ] || fail "expected one directory of packs: $dir"
[ "$(ls "$dir"/pack-*.paperlean 2>/dev/null | wc -l)" -ge 1 ] || fail "no module was packed: $(ls "$dir")"
tc="$PAPERLEAN_CACHE_DIR/toolchain-packs"
lib=$(ls "$tc"/lib-*.paperlean 2>/dev/null)
[ "$(echo "$lib" | wc -w | tr -d ' ')" = 1 ] || fail "expected one pack of the toolchain's library: $(ls "$tc")"
# (the pack and the record of its identity)
[ "$(ls "$tc" | wc -l | tr -d ' ')" = 2 ] || fail "files left in the cache directory: $(ls "$tc")"

# Every pack serves its files, with the same results as without packs. (The toolchain's pack alone
# serves files too, so the modules' packs must serve more.)
capture lake env lean Probe.lean
grep -v "served from packs" "$CAPTURED.out.produced" > "$TMP_DIR/expected.out"
served() { sed -n 's/^served from packs: \([0-9]*\)$/\1/p' "$CAPTURED.out.produced"; }
capture env LEAN_OLEAN_PACK="$lib" lake env lean Probe.lean
only_lib=$(served)
[ "${only_lib:-0}" -gt 0 ] || fail "the toolchain's pack serves nothing: $(cat "$CAPTURED.out.produced")"
packs="$lib:$(ls "$dir"/pack-*.paperlean | tr '\n' ':')"
capture env LEAN_OLEAN_PACK="$packs" lake env lean Probe.lean
[ "$(served)" -gt "$only_lib" ] || fail "the modules' packs serve nothing: $(served), $only_lib"
grep -v "served from packs" "$CAPTURED.out.produced" | $DIFF -- "$TMP_DIR/expected.out" - ||
  fail "the output with the packs differs"

# The next build removes the packs of the earlier one (another process), and its own at the end;
# the toolchain's pack is used again; of four packs of other toolchains, the two newest and the one in
# use (locked) are kept.
# (without the `flock` command, e.g. on macOS, no pack is locked and the oldest two go)
lib_inode=$(ls -i "$lib" | awk '{print $1}')
days_ago() { date -d "$1 days ago" +%Y%m%d%H%M.%S 2>/dev/null || date -v-"$1"d +%Y%m%d%H%M.%S; }
for i in 1 2 3 4; do
  echo old > "$tc/lib-0-old$i-x.paperlean"; touch -t "$(days_ago $i)" "$tc/lib-0-old$i-x.paperlean"
done
locked=''
if command -v flock > /dev/null; then
  locked=4
  exec 9< "$tc/lib-0-old4-x.paperlean"
  flock -s 9
fi
clean
run env PAPERLEAN_BUILD_PACKS=1 PAPERLEAN_BUILD_PACK_BATCH=1 lake build
[ -z "$locked" ] || exec 9<&-
[ ! -e "$dir" ] || fail "the packs of the earlier build were not removed"
[ -z "$(packdirs)" ] || fail "the build did not remove its packs: $(packdirs)"
[ "$(ls -i "$lib" | awk '{print $1}')" = "$lib_inode" ] || fail "the toolchain's pack was written again"
for i in 1 2 $locked; do
  [ -f "$tc/lib-0-old$i-x.paperlean" ] || fail "the toolchain pack old$i was removed: $(ls "$tc")"
done
[ ! -e "$tc/lib-0-old3-x.paperlean" ] || fail "the toolchain pack old3 was kept: $(ls "$tc")"
[ -n "$locked" ] || [ ! -e "$tc/lib-0-old4-x.paperlean" ] || fail "the toolchain pack old4 was kept: $(ls "$tc")"

# The temporary files of writers that ended are removed; a pack of the toolchain that cannot be read
# is written again.
touch "$lib.tmp.99999999" "$lib.tmp-99999998.tmp.99999998"
chmod u+w "$lib"
echo garbage > "$lib"
clean
run env PAPERLEAN_BUILD_PACKS=1 PAPERLEAN_BUILD_PACK_BATCH=1 lake build
[ ! -e "$lib.tmp.99999999" ] && [ ! -e "$lib.tmp-99999998.tmp.99999998" ] ||
  fail "temporary files were left: $(ls "$tc")"
[ "$(head -c 9 "$lib")" = PAPERLEAN ] || fail "the unreadable pack of the toolchain was not written again"

# Without the disk space for it (and a tenth more), the pack of the toolchain's library is not
# written; the build packs its modules all the same.
rm -f "$lib"
clean
run env PAPERLEAN_FREE_SPACE=1000 PAPERLEAN_BUILD_PACKS=1 PAPERLEAN_BUILD_PACK_BATCH=1 PAPERLEAN_BUILD_PACKS_KEEP=1 lake build
[ ! -e "$lib" ] || fail "the pack of the toolchain's library was written without the disk space for it"
[ -n "$(ls .lake/paperlean/build/*/pack-*.paperlean 2>/dev/null)" ] || fail "no module was packed"
rm -rf .lake/paperlean/build

# With prepared data, no packs are written.
clean
run lake build
run lake paperlean build --prepare=root
touch Root/D.lean
run env PAPERLEAN_BUILD_PACKS=1 PAPERLEAN_BUILD_PACKS_KEEP=1 lake build
[ -z "$(packdirs)" ] || fail "a build with prepared data wrote packs: $(packdirs)"

# The packs of a build that was interrupted (whose process ended) are removed by the next
# `paperlean build`, also one that does not pack, and by `paperlean prepare`.
mkdir -p .lake/paperlean/build/99999999; touch .lake/paperlean/build/99999999/pack-0.paperlean
run lake paperlean build
[ ! -e .lake/paperlean/build/99999999 ] || fail "paperlean build kept the packs of a build that ended"
mkdir -p .lake/paperlean/build/99999999; touch .lake/paperlean/build/99999999/pack-0.paperlean
run lake paperlean prepare root --no-native
[ ! -e .lake/paperlean/build/99999999 ] || fail "prepare kept the packs of a build that ended"
