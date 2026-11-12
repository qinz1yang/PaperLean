# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests a build's mid-build preparation (`src/lake/Lake/PaperLean/MidBuild.lean`): after an early
# fraction of a package without prepared data, `paperlean build` pauses its compile scheduler,
# prepares the modules that are built and gives the later `lean` processes the new data. The outputs
# are byte-identical to a build with the feature off; the feature runs only under `paperlean build`
# (not plain `lake build`), not for a package below the size threshold, and a failed preparation
# leaves the build on the interpreter path with the same outputs. A required package without built
# modules (`empty`) has an empty pack, which no preparation may try to bind. Without root imports, the
# import image of a preparation during a dependency's own build describes its built modules.

WS="$(cd "$TMP_DIR" && pwd -P)/ws"
DEP="$TMP_DIR/dep"
EMPTY="$TMP_DIR/empty"
mkdir -p "$WS/Root" "$DEP/Dep" "$EMPTY"
cat > "$EMPTY/lakefile.toml" <<'END'
name = "empty"
defaultTargets = ["Empty"]
[[lean_lib]]
name = "Empty"
END
printf 'def emptyValue : Nat := 0\n' > "$EMPTY/Empty.lean"
cat > "$DEP/lakefile.toml" <<'END'
name = "dep"
defaultTargets = ["Dep"]
[[lean_lib]]
name = "Dep"
globs = ["Dep.+", "Dep"]
END
cat > "$DEP/Dep/A0Tactic.lean" <<'END'
import Lean
open Lean Elab Tactic
initialize registerTraceClass `depDemo
elab "dep_tac" : tactic => do
  evalTactic (← `(tactic| decide))
END
cat > "$DEP/Dep/B1.lean" <<'END'
import Dep.A0Tactic
def b1 : Nat := 1
example : 1 = 1 := by dep_tac
END
cat > "$DEP/Dep/B2.lean" <<'END'
import Dep.B1
def b2 : Nat := b1 + 1
END
cat > "$DEP/Dep/B3.lean" <<'END'
import Dep.B2
example : 2 = 2 := by dep_tac
END
cat > "$DEP/Dep/B4.lean" <<'END'
import Dep.B3
example : 3 = 3 := by dep_tac
END
cat > "$DEP/Dep.lean" <<'END'
import Dep.B4
#eval show IO Unit from do
  let packs := (← IO.getEnv "LEAN_OLEAN_PACK").getD ""
  let native := (← IO.getEnv "PAPERLEAN_NATIVE_LIBS").getD ""
  let hasPack := packs.contains "bind/dep-"
  let hasNative := native.contains "/native/dep-"
  let marker := (← IO.getEnv "PAPERLEAN_DATA").getD "none"
  let mid := (← IO.getEnv "PAPERLEAN_MIDBUILD").getD "none"
  let accel := (← IO.getEnv "PAPERLEAN_ACCELERATE").getD "none"
  let sched := (← IO.getEnv "PAPERLEAN_SCHEDULE").getD "none"
  let slots := (← IO.getEnv "PAPERLEAN_SCHEDULE_SLOTS").getD "none"
  IO.println s!"midbuild-probe packs={hasPack} native={hasNative} marker={marker} mid={mid} accel={accel} sched={sched} slots={slots}"
END
cd "$WS"
cat > lakefile.toml <<'END'
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "dep"
path = "../dep"
[[require]]
name = "empty"
path = "../empty"
[[lean_lib]]
name = "Root"
END
printf 'def rootValue : Nat := 0\n' > Root.lean

# The outputs of the dependency, relative to $TMP_DIR, and a copy of them.
outputs() {
  (cd "$TMP_DIR" && for d in dep/.lake/build ws/.lake/build; do
    [ -d "$d" ] && find "$d" -type f \
      \( -name '*.olean' -o -name '*.olean.server' -o -name '*.olean.private' -o -name '*.ilean' -o -name '*.c' \) || true
  done | sort)
}
copy_outputs() {
  local dst="$1"
  mkdir -p "$dst"
  for f in $(outputs); do mkdir -p "$dst/$(dirname "$f")"; cp "$TMP_DIR/$f" "$dst/$f"; done
}
same_outputs() {
  [ "$(cd "$TMP_DIR" && find ref -type f | sed 's|^ref/||' | sort)" = "$(outputs)" ] ||
    fail "the file set differs from the build without the feature"
  for f in $(cd "$TMP_DIR" && find ref -type f | sed 's|^ref/||'); do
    cmp -s "$TMP_DIR/ref/$f" "$TMP_DIR/$f" || fail "$f differs from the build without the feature"
  done
}
clean_outputs() {
  rm -rf .lake/build "$DEP/.lake/build"
  rm -f .lake/paperlean-times.paperlean*
}
diagnostics() { grep -E 'warning:|error:|info:' "$1" | grep -v -e 'mid-build' -e '^paperlean:' -e 'midbuild-probe' | sort || true; }

# Prepare the dependencies before the package has built modules: its prepared data is empty, as in
# the release's clean build.
run lake paperlean prepare
cp .lake/paperlean/env.json "$TMP_DIR/env.initial"
# The dependency imports that make the build partial: root now imports the whole dep umbrella, so at
# the cut some dependency modules that root imports are not built (`PrepareOptions.allowPartial`).
printf 'import Dep\ndef rootValue : Nat := 0\n' > Root.lean
python3 - <<'END'
import json
d = json.load(open(".lake/paperlean/env.json"))
p = [x for x in d["deps"] if x["pkg"] == "dep"]
assert p and p[0]["pack"] == "", p
END

# The reference: the same builds without the feature.
clean_outputs
capture env PAPERLEAN_MIDBUILD=0 PAPERLEAN_SCHEDULE_SLOTS=1 lake paperlean build +Root
check_out_contains "midbuild-probe packs=false native=false"
copy_outputs "$TMP_DIR/ref"
diagnostics "$CAPTURED.out.produced" > "$TMP_DIR/ref.diagnostics"

# A failed preparation falls back: the build succeeds, its data is unchanged and its outputs equal.
clean_outputs
cp "$TMP_DIR/env.initial" .lake/paperlean/env.json
# It runs before any successful preparation, so no pack of dep is in the cache and whatever the batch is
# (the modules finished when the build pauses, plus any that were compiling then) a new pack must be written;
# with an empty free-space budget it cannot be, so this is a real packing failure. The threshold (2 of dep's 6
# modules) is reached in the middle of the build, so the paused build waits for the failed preparation and
# reports it (a threshold reached only by the last module would race the build's end, when nothing is left
# that the preparation could help, and the session rightly skips it).
capture env PAPERLEAN_MIDBUILD=1 PAPERLEAN_MIDBUILD_MIN=2 PAPERLEAN_MIDBUILD_DIV=3 \
  PAPERLEAN_SCHEDULE_SLOTS=1 PAPERLEAN_FREE_SPACE=0 lake paperlean build +Root
check_out_contains "paperlean: mid-build preparation of dep did not finish"
[ "$(grep -c 'mid-build preparation of dep: the build pauses' "$CAPTURED.out.produced")" -eq 1 ] ||
  fail "the failed preparation was started more than once"
! grep -Fq "takes longer than" "$CAPTURED.out.produced" || fail "a failed preparation was reported as a timeout"
cmp -s "$TMP_DIR/env.initial" .lake/paperlean/env.json ||
  fail "a failed preparation changed the prepared data"
same_outputs

# With the feature (its size threshold lowered to this small project): it prepares dep after three
# of its six modules, and the modules after it compile from the new data. The outputs are equal.
clean_outputs
cp "$TMP_DIR/env.initial" .lake/paperlean/env.json
capture env PAPERLEAN_MIDBUILD=1 PAPERLEAN_MIDBUILD_MIN=2 PAPERLEAN_MIDBUILD_DIV=2 \
  PAPERLEAN_SCHEDULE_SLOTS=1 lake paperlean build +Root
check_out_contains "paperlean: mid-build prepared dep"
check_out_contains "midbuild-probe packs=true native=true"
! grep -Fq "cannot bind" "$CAPTURED.out.produced" || fail "a preparation tried to bind an empty pack"
check_out_contains "Built Dep.B4"
mid=$(grep -m 1 -n "mid-build prepared dep" "$CAPTURED.out.produced" | cut -d: -f1)
[[ $mid =~ ^[0-9]+$ ]] || fail "no line number for the preparation's message"
# (a `Built` line AFTER the preparation's line: compare line numbers, `NR`, not a line's text)
later=$(awk -v m="$mid" 'NR > m && /Built / {print; exit}' "$CAPTURED.out.produced")
[ -n "$later" ] || fail "no module was built after the preparation"
same_outputs
diagnostics "$CAPTURED.out.produced" > "$TMP_DIR/mid.diagnostics"
$DIFF -- "$TMP_DIR/ref.diagnostics" "$TMP_DIR/mid.diagnostics" ||
  fail "the build's diagnostics differ from the build without the feature"
python3 - <<'END'
import json
d = json.load(open(".lake/paperlean/env.json"))
p = [x for x in d["deps"] if x["pkg"] == "dep"]
assert p and p[0]["pack"], p
l = [x for x in d["libs"] if x["pkg"] == "dep"]
assert l and l[0]["modules"] > 0, l
END

# Plain `lake build` does not prepare anything, even with the feature's variables set.
clean_outputs
cp "$TMP_DIR/env.initial" .lake/paperlean/env.json
capture env PAPERLEAN_MIDBUILD=1 PAPERLEAN_MIDBUILD_MIN=2 PAPERLEAN_MIDBUILD_DIV=2 \
  PAPERLEAN_SCHEDULE_SLOTS=1 lake build +Root
! grep -Fq "mid-build" "$CAPTURED.out.produced" || fail "plain lake build prepared part of the package"
cmp -s "$TMP_DIR/env.initial" .lake/paperlean/env.json || fail "plain lake build changed the prepared data"

# A package below the default size threshold is not prepared: a small project pays nothing.
clean_outputs
cp "$TMP_DIR/env.initial" .lake/paperlean/env.json
capture lake paperlean build +Root
! grep -Fq "mid-build" "$CAPTURED.out.produced" || fail "a small build prepared part of its package"
cmp -s "$TMP_DIR/env.initial" .lake/paperlean/env.json || fail "a small build changed the prepared data"

# A workspace whose root package imports nothing of the package that it builds (as a clean build of Mathlib in
# a project without modules of its own): the candidates of the import image are the dependencies' roots, which
# import all of their modules. At the cut the root of `dep2` (one library with its default glob, as Mathlib's)
# is not built, so its built modules stand for it: the image of the mid-build preparation describes them (it
# described none before). The outputs are those of the build without the feature.
WS2="$(cd "$TMP_DIR" && pwd -P)/ws2"
DEP2="$TMP_DIR/dep2"
mkdir -p "$WS2" "$DEP2/Dep2"
cat > "$DEP2/lakefile.toml" <<'END'
name = "dep2"
defaultTargets = ["Dep2"]
[[lean_lib]]
name = "Dep2"
END
cat > "$DEP2/Dep2/A0Tactic.lean" <<'END'
import Lean
open Lean Elab Tactic
elab "dep2_tac" : tactic => do
  evalTactic (← `(tactic| decide))
END
prev=A0Tactic
for i in 1 2 3 4; do
  printf 'import Dep2.%s\nexample : %d = %d := by dep2_tac\ntheorem dep2_t%d : %d + 0 = %d := by simp\n' \
    "$prev" "$i" "$i" "$i" "$i" "$i" > "$DEP2/Dep2/B$i.lean"
  prev=B$i
done
printf 'import Dep2.B4\n' > "$DEP2/Dep2.lean"
cat > "$WS2/lakefile.toml" <<'END'
name = "root2"
defaultTargets = ["Root2"]
[[require]]
name = "dep2"
path = "../dep2"
[[lean_lib]]
name = "Root2"
END
printf 'def root2Value : Nat := 0\n' > "$WS2/Root2.lean"
cd "$WS2"
run lake paperlean prepare
cp .lake/paperlean/env.json "$TMP_DIR/env2.initial"
outputs2() {
  (cd "$TMP_DIR" && find dep2/.lake/build -type f \
    \( -name '*.olean' -o -name '*.olean.server' -o -name '*.olean.private' -o -name '*.ilean' -o -name '*.c' \) | sort)
}
capture env PAPERLEAN_MIDBUILD=0 PAPERLEAN_SCHEDULE_SLOTS=1 lake paperlean build Dep2
for f in $(outputs2); do mkdir -p "$TMP_DIR/ref2/$(dirname "$f")"; cp "$TMP_DIR/$f" "$TMP_DIR/ref2/$f"; done
rm -rf "$DEP2/.lake/build" .lake/paperlean-times.paperlean*
cp "$TMP_DIR/env2.initial" .lake/paperlean/env.json
capture env PAPERLEAN_MIDBUILD=1 PAPERLEAN_MIDBUILD_MIN=2 PAPERLEAN_MIDBUILD_DIV=2 \
  PAPERLEAN_SCHEDULE_SLOTS=1 lake paperlean build Dep2
check_out_contains "paperlean: mid-build prepared dep2"
images=$(sed -n 's/^Writing the import image of \([0-9][0-9]*\) modules.*/\1/p' "$CAPTURED.out.produced" | tail -n 1)
[ "${images:-0}" -ge 3 ] ||
  fail "the mid-build preparation's import image describes ${images:-no} modules, not dep2's built ones"
[ "$(cd "$TMP_DIR" && find ref2 -type f | sed 's|^ref2/||' | sort)" = "$(outputs2)" ] ||
  fail "dep2's file set differs from the build without the feature"
for f in $(outputs2); do
  cmp -s "$TMP_DIR/ref2/$f" "$TMP_DIR/$f" || fail "$f differs from the build without the feature"
done
