# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests the order of work of builds under `paperlean` commands (`PAPERLEAN_ACCELERATE`): their compiles
# (`src/lake/Lake/PaperLean/Schedule.lean`) and their reading of headers ahead (`Module.recFetchInput`),
# which plain `lake` does not do: the modules compile to the same files and traces as without it; with
# one slot, the slot goes to the module with the longest path to the end of the build, by the sizes of
# the sources or by the compile times that earlier builds recorded in
# `.lake/paperlean-times.paperlean` (a damaged record, or one of another build, is ignored); a module
# that fails fails the build as without it, with the modules that do not import it built; builds whose
# jobs end before they compile (a failed `needs`, `--fail-fast`, a facet without the module's build)
# end as without it; modules of the same name in two packages all compile; no more processes run at
# a time than without it; `--no-build` exits as without it; an import cycle is reported as without it. Every build here is bounded in time, as a
# build that hangs would be the failure.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN PAPERLEAN_DATA PAPERLEAN_BUILD_PACKS PAPERLEAN_SCHEDULE PAPERLEAN_SCHEDULE_SLOTS
unset PAPERLEAN_SCHEDULE_KEEP
WS="$(cd "$TMP_DIR" && pwd -P)/ws"
mkdir -p "$WS/Root"
cd "$WS"
cat > lakefile.toml <<'END'
name = "root"
defaultTargets = ["Root"]
[[lean_lib]]
name = "Root"
END
# A chain A <- L1 <- L2 <- L3 beside the short S1, S2, S3, all below Root; the chain's sources are
# larger, so that it is longer by their sizes
printf 'def a : Nat := 1\n' > Root/A.lean
pad=$(printf -- '-- padding%.0s' $(seq 200))
printf 'import Root.A\ndef l1 : Nat := a + 1\n%s\n' "$pad" > Root/L1.lean
printf 'import Root.L1\ndef l2 : Nat := l1 + 1\n%s\n' "$pad" > Root/L2.lean
printf 'import Root.L2\ndef l3 : Nat := l2 + 1\n%s\n' "$pad" > Root/L3.lean
for s in S1 S2 S3; do printf "import Root.A\ndef ${s}v : Nat := a\n" > Root/$s.lean; done
printf 'import Root.L3\nimport Root.S1\nimport Root.S2\nimport Root.S3\n' > Root.lean
REC=.lake/paperlean-times.paperlean
outputs() { (cd "$WS" && find .lake/build -name '*.olean*' -o -name '*.ilean' -o -name '*.ir*' -o -name '*.c' -o -name '*.trace' | sort); }
order() { grep -o 'Built Root[.A-Za-z0-9]*' "$CAPTURED.out.produced" | sed 's/Built //' | tr '\n' ' '; }
# a command, killed after $1 seconds (exit code 142)
lim() { local n=$1; shift; perl -e 'alarm shift; exec @ARGV' "$n" "$@"; }

# Plain `lake`: the reference files; no record.
run lim 120 lake build
for f in $(outputs); do mkdir -p "$TMP_DIR/ref/$(dirname "$f")"; cp "$f" "$TMP_DIR/ref/$f"; done
[ ! -e "$REC" ] || fail "plain lake recorded compile times"
same_files() {
  for f in $(outputs); do
    cmp -s "$f" "$TMP_DIR/ref/$f" || fail "$f differs from the build without scheduling"
  done
  [ "$(outputs | wc -l)" = "$(cd "$TMP_DIR/ref" && find .lake -type f | wc -l)" ] || fail "other files"
}
export PAPERLEAN_ACCELERATE=1

# One slot: the chain first, by the sizes of the sources; the same files. (A slot is kept here for
# long enough for its module to ask for it on a busy machine: the 50 ms of a normal build may let it
# go to the next module, which is not the order that is tested.)
export PAPERLEAN_SCHEDULE_KEEP=5000
rm -rf .lake/build
capture lim 120 env PAPERLEAN_SCHEDULE_SLOTS=1 lake build
case "$(order)" in "Root.A Root.L1 Root.L2 Root.L3 "*) ;; *) fail "not the chain first: $(order)" ;; esac
same_files
header=$(head -1 "$REC")
case "$header" in "paperlean-times 2 "*"+$(lake paperlean --version | sed -n 's/^build //p') "*) ;;
  *) fail "the record does not name its build: $header" ;; esac
grep -q ' root/Root.L2$' "$REC" || fail "Root.L2 is not recorded"
[ ! -e .lake/paperlean ] || fail "the records made .lake/paperlean, without prepared data"

# By recorded times: S2, recorded as slow, goes before the chain.
printf '%s\n100000 root/Root.S2\n10 root/Root.L1\n10 root/Root.L2\n10 root/Root.L3\n' "$header" > "$REC"
rm -rf .lake/build
capture lim 120 env PAPERLEAN_SCHEDULE_SLOTS=1 lake build
case "$(order)" in "Root.A Root.S2 "*) ;; *) fail "the slow module did not go first: $(order)" ;; esac
same_files
# its time measured now replaces the recorded one
! grep -q '^100000 root/Root.S2$' "$REC" || fail "the record was not updated"

# A record of another build, or a damaged one, is ignored and written again; so are the temporary
# files of writers that ended.
for bad in "paperlean-times 2 0.0.0+000000000000 0000" garbage; do
  printf '%s\n100000 root/Root.S2\n' "$bad" > "$REC"
  touch "$REC.tmp.99999999"
  rm -rf .lake/build
  capture lim 120 env PAPERLEAN_SCHEDULE_SLOTS=1 lake build
  case "$(order)" in "Root.A Root.L1 Root.L2 Root.L3 "*) ;; *) fail "not the chain first: $(order)" ;; esac
  same_files
  [ "$(head -1 "$REC")" = "$header" ] || fail "the record '$bad' was kept"
  [ ! -e "$REC.tmp.99999999" ] || fail "the temporary file of a writer that ended was kept"
done

# Several slots, and the scheduler turned off: the same files.
unset PAPERLEAN_SCHEDULE_KEEP
rm -rf .lake/build
run lim 120 env PAPERLEAN_SCHEDULE_SLOTS=3 lake build
same_files
rm -rf .lake/build
run lim 120 env PAPERLEAN_SCHEDULE=0 lake build
same_files

# A module that fails: the build fails, reporting it, and builds the modules that do not import it;
# with `--fail-fast` it ends too.
printf 'import Root.A\ndef bad : Nat := "no"\n' > Root/S2.lean
rm -rf .lake/build
capture_exit 1 lim 120 env PAPERLEAN_SCHEDULE_SLOTS=1 lake build
check_out_contains "Root.S2"
check_out_contains "error"
for m in A L1 L2 L3 S1 S3; do [ -f .lake/build/lib/lean/Root/$m.olean ] || fail "Root.$m was not built"; done
[ ! -f .lake/build/lib/lean/Root.olean ] || fail "Root was built"
for slots in 1 3; do
  rm -rf .lake/build
  capture_exit 1 lim 120 env PAPERLEAN_SCHEDULE_SLOTS=$slots lake build --fail-fast
done
printf 'import Root.A\ndef S2v : Nat := a\n' > Root/S2.lean

# A facet that builds the imports of a module but not the module itself.
rm -rf .lake/build
capture lim 120 lake build Root.L2:deps
[ -f .lake/build/lib/lean/Root/L1.olean ] && [ ! -f .lake/build/lib/lean/Root/L2.olean ] ||
  fail "Root.L2:deps did not build the imports of Root.L2 alone"

# `--no-build` exits as without scheduling.
capture_exit 3 lim 120 lake build --no-build
capture_exit 3 lim 120 env PAPERLEAN_ACCELERATE= lake build --no-build
run lim 120 lake build
run lim 120 lake build --no-build

# A library that `needs` a missing file and imports a module that compiles: the build fails, as
# without scheduling, building everything else, also with one slot.
mkdir -p "$TMP_DIR/needs/Base" && cd "$TMP_DIR/needs"
cat > lakefile.toml <<'END'
name = "needs"
defaultTargets = ["Base", "Top"]
[[input_file]]
name = "missing"
path = "inputs/missing.txt"
[[lean_lib]]
name = "Base"
[[lean_lib]]
name = "Top"
needs = ["missing"]
END
printf 'def a : Nat := 1\n' > Base/A.lean
printf 'import Base.A\ndef b1 : Nat := a\n' > Base/B1.lean
printf 'import Base.A\ndef b2 : Nat := a\n' > Base/B2.lean
printf 'import Base.B1\nimport Base.B2\n' > Base.lean
printf 'import Base.A\ndef t : Nat := a\n' > Top.lean
for slots in 1 3; do
  rm -rf .lake/build
  capture_exit 1 lim 120 env PAPERLEAN_SCHEDULE_SLOTS=$slots lake build
  for m in Base/A Base/B1 Base/B2 Base; do
    [ -f .lake/build/lib/lean/$m.olean ] || fail "$m was not built with $slots slot(s)"
  done
done
cd "$WS"

# Modules of the same names in two packages, compiled at the same time.
mkdir -p "$TMP_DIR/dup/Shared" "$TMP_DIR/dup/dep/Shared" && cd "$TMP_DIR/dup"
printf 'name = "dep"\n[[lean_lib]]\nname = "Shared"\nglobs = ["Shared.+"]\n[[lean_lib]]\nname = "DBase"\n' > dep/lakefile.toml
printf 'def base : Nat := 1\n' > dep/DBase.lean
printf 'name = "dup"\n[[require]]\nname = "dep"\npath = "dep"\n[[lean_lib]]\nname = "Shared"\nglobs = ["Shared.+"]\n' > lakefile.toml
for i in $(seq 24); do
  printf "import DBase\ndef m$i : Nat := $i + base\n" > Shared/M$i.lean
  cp Shared/M$i.lean dep/Shared/M$i.lean
done
for k in 1 2 3 4 5 6; do
  rm -rf .lake/build dep/.lake/build
  capture lim 120 lake build Shared @dep/Shared
  for i in $(seq 24); do
    [ -f .lake/build/lib/lean/Shared/M$i.olean ] && [ -f dep/.lake/build/lib/lean/Shared/M$i.olean ] ||
      fail "Shared.M$i was not built in both packages"
  done
done
cd "$WS"

# Lean's compiles share the task manager's threads with the build's other processes (here those of
# precompiled modules): no more of them at a time than without scheduling.
mkdir -p "$TMP_DIR/procs-ws/P" && cd "$TMP_DIR/procs-ws"
printf 'name = "p"\ndefaultTargets = ["P"]\n[[lean_lib]]\nname = "P"\nprecompileModules = true\n' > lakefile.toml
for i in $(seq 16); do
  printf "def f$i (n : Nat) : Nat := Id.run do\n  let mut s := 0\n  for i in [0:n] do s := s + i * $i\n  return s\n" > P/M$i.lean
done
for i in $(seq 16); do echo "import P.M$i"; done > P.lean
# the most processes of this workspace's build at a time, sampled while `lake build` runs with $1
most() {
  rm -rf .lake/build "$TMP_DIR/procs-stop"; : > "$TMP_DIR/procs"
  # (`set +e`: `grep -c` fails when it counts none)
  ( set +e; while [ ! -e "$TMP_DIR/procs-stop" ]; do
      ps -A -o command | grep -c "^[^ ]*\(lean\|clang\|ld\|cc\) .*/procs-ws/" >> "$TMP_DIR/procs"
      sleep 0.01
    done ) &
  local w=$!
  lim 120 env PAPERLEAN_ACCELERATE=$1 LEAN_NUM_THREADS=2 lake build > "$TMP_DIR/procs-out" 2>&1 ||
    { touch "$TMP_DIR/procs-stop"; wait $w; cat "$TMP_DIR/procs-out"; fail "the build of precompiled modules failed"; }
  touch "$TMP_DIR/procs-stop"; wait $w
  most=$(sort -n "$TMP_DIR/procs" | tail -1)
}
# (not in a command substitution, in whose subshell `fail` would end only the subshell)
most ""
plain=$most
most 1
accelerated=$most
[ "$accelerated" -le "$plain" ] || fail "$accelerated processes at a time, plain lake $plain"
cd "$WS"

# An import cycle is reported as with plain `lake`.
printf 'import Root.S2\ndef a : Nat := 1\n' > Root/A.lean
rm -rf .lake/build
capture_exit 1 lim 120 env PAPERLEAN_ACCELERATE= lake build
report() { grep -v '^+' "$CAPTURED.out.produced" | sed 's/ ([0-9.]*m*s)$//'; }
report > "$TMP_DIR/cycle-plain.out"
check_out_contains "build cycle detected"
rm -rf .lake/build
capture_exit 1 lim 120 lake build
report | $DIFF -- "$TMP_DIR/cycle-plain.out" - ||
  fail "the import cycle is reported otherwise than by plain lake"
