# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests the writer ownership of mid-build preparations (`src/lake/Lake/PaperLean/MidBuild.lean`), with test
# gates that hold a preparation at a chosen point (`PAPERLEAN_NATIVE_COMPILER_GATE`, and
# `PAPERLEAN_MIDBUILD_{START,RELOAD,RESUME}_GATE`: `<dir>/<tag>` is written, `<dir>/<tag>.go` lets it go on):
# (1) Two packages qualify. The first one's writer is held (native compiler gate) past the build's last
#     compile while its wait times out at once and the build resumes. No second writer may start while
#     the first runs (both would publish the workspace's prepared data; preparations during a build take
#     no data lock). The build stays open until the writer ends, then ends normally, with the outputs of
#     the build without the feature.
# (2) The writer has taken the right to replace the build's environment (held right after that) when the
#     build's wait times out: the build must wait for the replacement instead of resuming compiles under
#     it. While the writer is held, the set of compiled modules must not change although compiles are
#     pending; afterwards the later compiles use the new data and no timeout is reported.
# (3) The preparation tasks of a dependency (pa) and of the root package are both dispatched; the
#     root's is held before it asks for ownership. pa prepares; its writer ends; its coordinator is held
#     right before it resumes the scheduler. Then the root's task goes on: it must NOT get ownership (and
#     pause, prepare, reach its writer) before pa's coordinator has resumed the scheduler: the scheduler's
#     resume has no owner, so pa's coordinator would lift the root preparation's pause. A later
#     preparation of the root must keep its pause while its writer is held. (The root is the second
#     contender because a dependency's preparation also packs the other built dependencies, which makes
#     them ineligible, but leaves the root's packs alone.)
# Run as an ordinary user. (`MIDBUILD_WRITER_CASES`, for evaluating builds: which cases run; all by default.)

ROOT="$(cd "$TMP_DIR" && pwd -P)"
WS="$ROOT/ws"
mkdir -p "$WS"
N_CHAIN=6   # modules A0..A5 and the library root: the cut (half of 7, rounded up: 4) leaves compiles pending
mkpkg() { # mkpkg <dir> <Lib>: a chain of modules, the last one printing whether it sees its package's pack
  local d="$ROOT/$1" L=$2 i
  mkdir -p "$d/$L"
  cat > "$d/lakefile.toml" <<END
name = "$1"
defaultTargets = ["$L"]
[[lean_lib]]
name = "$L"
END
  # (names of their own per package: the root imports both, and its import image needs them distinct)
  printf 'def %s_a0 : Nat := 0\n' "$1" > "$d/$L/A0.lean"
  for ((i = 1; i < N_CHAIN; i++)); do
    printf 'import %s.A%d\ndef %s_a%d : Nat := %s_a%d + 1\n' "$L" $((i - 1)) "$1" $i "$1" $((i - 1)) > "$d/$L/A$i.lean"
  done
  cat > "$d/$L.lean" <<END
import $L.A$((N_CHAIN - 1))
#eval show IO Unit from do
  IO.println s!"writer-probe $L packs={decide ((((← IO.getEnv "LEAN_OLEAN_PACK").getD "").splitOn "bind/$1-").length > 1)}"
END
}
mkpkg pa PA
mkpkg pb PB
cat > "$WS/lakefile.toml" <<'END'
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "pa"
path = "../pa"
[[require]]
name = "pb"
path = "../pb"
[[lean_lib]]
name = "Root"
END
# the root package's library: a chain of its own, R0..R14 and Root (16 modules, so its cut is 8). It is longer
# than pa's (7): the build compiles the longest remaining chain first, so 9 root modules come before any
# of pa's, and the root's preparation task is dispatched before pa's (case 3).
N_ROOT=15
mkdir -p "$WS/Root"
printf 'def root_r0 : Nat := 0\n' > "$WS/Root/R0.lean"
for ((i = 1; i < N_ROOT; i++)); do
  printf 'import Root.R%d\ndef root_r%d : Nat := root_r%d + 1\n' $((i - 1)) $i $((i - 1)) > "$WS/Root/R$i.lean"
done
printf 'import Root.R%d\ndef rootValue : Nat := root_r%d\n' $((N_ROOT - 1)) $((N_ROOT - 1)) > "$WS/Root.lean"
cd "$WS"
outputs() { # outputs [<build dir>...]: the output files of the given build directories (default: pa's, pb's)
  local dirs=("$@"); [ ${#dirs[@]} -gt 0 ] || dirs=(pa/.lake/build pb/.lake/build)
  (cd "$ROOT" && for d in "${dirs[@]}"; do
    [ -d "$d" ] && find "$d" -type f \( -name '*.olean' -o -name '*.ilean' -o -name '*.c' \) || true
  done | sort)
}
# (the tests run under `set -e -o pipefail`: helpers whose commands may fail must not end the test silently)
compiled() { (cd "$ROOT" && { find pa/.lake/build pb/.lake/build ws/.lake/build -name '*.olean' 2>/dev/null || true; } | sort); }
clean_outputs() { rm -rf "$ROOT/pa/.lake/build" "$ROOT/pb/.lake/build" "$WS/.lake/build" .lake/paperlean-times.paperlean*; }
keep_ref() { # keep_ref <ref dir> [<build dir>...]: keep the build's outputs as the reference
  local r=$1 f; shift
  rm -rf "$r"; mkdir -p "$r"
  for f in $(outputs "$@"); do mkdir -p "$r/$(dirname "$f")"; cp "$ROOT/$f" "$r/$f"; done
}
same_outputs() { # same_outputs <case> <ref dir> [<build dir>...]
  local c=$1 r=$2 f; shift 2
  [ "$(cd "$r" && find . -type f | sed 's|^\./||' | sort)" = "$(outputs "$@")" ] || fail "$c: the file set differs"
  for f in $(outputs "$@"); do cmp -s "$r/$f" "$ROOT/$f" || fail "$c: $f differs from the build without the feature"; done
}
run lake paperlean prepare
cp .lake/paperlean/env.json "$ROOT/env.initial"
# the reference: the same build without the feature
clean_outputs
capture env PAPERLEAN_MIDBUILD=0 PAPERLEAN_SCHEDULE_SLOTS=1 lake paperlean build PA PB
keep_ref "$ROOT/ref"
NALL=$(compiled | wc -l)
wait_for() { # wait_for <seconds> <command>...: poll until the command succeeds
  local n=$(( $1 * 10 )); shift
  for ((; n > 0; n--)); do "$@" && return 0; sleep 0.1; done
  return 1
}
blocked_count() { { find "$1" -maxdepth 1 -name 'blocked-*' 2>/dev/null || true; } | wc -l; }
any_blocked() { [ "$(blocked_count "$1")" -gt 0 ]; }
all_compiled() { [ "$(compiled | wc -l)" -ge "$NALL" ]; }
not_running() { ! kill -0 "$1" 2>/dev/null; }
stop() { kill "$1" 2>/dev/null || true; wait "$1" 2>/dev/null || true; }
finish() { # finish <pid> <log> <case>: the build ends (within four minutes) with exit 0
  wait_for 240 not_running "$1" || { stop "$1"; cat "$2"; fail "$3 the build did not end"; }
  local rc=0; wait "$1" || rc=$?
  cat "$2"
  [ "$rc" = 0 ] || fail "$3 the build failed (exit $rc)"
}
GO() { : > "$1.go"; }
CASES=${MIDBUILD_WRITER_CASES:-123}

# (1) two packages, the first writer held past the build's last compile
if [[ $CASES == *1* ]]; then
  clean_outputs
  cp "$ROOT/env.initial" .lake/paperlean/env.json
  G="$ROOT/gate1"; rm -rf "$G"; mkdir -p "$G"
  PAPERLEAN_MIDBUILD=1 PAPERLEAN_MIDBUILD_MIN=2 PAPERLEAN_MIDBUILD_DIV=2 PAPERLEAN_MIDBUILD_PREP_MS=300 \
    PAPERLEAN_SCHEDULE_SLOTS=1 PAPERLEAN_NATIVE_COMPILER_GATE="$G" PAPERLEAN_NATIVE_COMPILER_GATE_INPUT=/A0.c \
    lake paperlean build PA PB > "$ROOT/build1.log" 2>&1 &
  BUILD=$!
  wait_for 240 any_blocked "$G" || { stop $BUILD; cat "$ROOT/build1.log"; fail "(1) no writer reached the gate"; }
  wait_for 240 all_compiled || { : > "$G/release"; wait $BUILD || true; cat "$ROOT/build1.log"; fail "(1) the build did not compile everything while the writer was held"; }
  sleep 3   # (time for a second package's writer to reach the gate, if one were started)
  n=$(blocked_count "$G")
  if not_running $BUILD; then
    : > "$G/release"; cat "$ROOT/build1.log"; fail "(1) the build ended while its writer was still running"
  fi
  : > "$G/release"
  finish $BUILD "$ROOT/build1.log" "(1)"
  [ "$n" = 1 ] || fail "(1) $n writers were running at once (a second package started one while the first still ran)"
  [ "$(grep -c 'the build pauses its compiles' "$ROOT/build1.log")" = 1 ] || fail "(1) more than one preparation started"
  grep -q "takes longer than 300 ms" "$ROOT/build1.log" || fail "(1) the timeout was not reported"
  same_outputs "(1)" "$ROOT/ref"
fi

# (2) the writer has taken the build's environment when the build's wait times out
if [[ $CASES == *2* ]]; then
  clean_outputs
  cp "$ROOT/env.initial" .lake/paperlean/env.json
  G="$ROOT/gate2"; rm -rf "$G"; mkdir -p "$G"
  PAPERLEAN_MIDBUILD=1 PAPERLEAN_MIDBUILD_MIN=2 PAPERLEAN_MIDBUILD_DIV=2 PAPERLEAN_MIDBUILD_PREP_MS=60000 \
    PAPERLEAN_SCHEDULE_SLOTS=1 PAPERLEAN_MIDBUILD_RELOAD_GATE="$G" \
    lake paperlean build PA > "$ROOT/build2.log" 2>&1 &
  BUILD=$!
  wait_for 240 test -f "$G/claimed" || { stop $BUILD; cat "$ROOT/build2.log"; fail "(2) the writer did not reach the reload gate"; }
  # (what was compiled when the writer took the environment; a later module must still be pending, or
  # the check below would hold whatever the build did)
  compiled > "$ROOT/at-claim"
  if grep -q "/PA.olean$" "$ROOT/at-claim"; then GO "$G/claimed"; wait $BUILD || true; fail "(2) nothing was left to compile when the writer was held"; fi
  sleep 70  # (past PAPERLEAN_MIDBUILD_PREP_MS, which the build's wait started before the writer claimed)
  compiled > "$ROOT/at-release"
  GO "$G/claimed"
  finish $BUILD "$ROOT/build2.log" "(2)"
  $DIFF -- "$ROOT/at-claim" "$ROOT/at-release" ||
    fail "(2) compiles went on while the writer was replacing the build's environment"
  ! grep -q "takes longer than" "$ROOT/build2.log" || fail "(2) a timeout was reported although the writer had taken the environment"
  grep -q "mid-build prepared pa" "$ROOT/build2.log" || fail "(2) the preparation was not given to the build"
  grep -q "writer-probe PA packs=true" "$ROOT/build2.log" || fail "(2) a later compile did not use the new data"
fi

# (3) the first coordinator still has to resume the scheduler when a second task asks for ownership
if [[ $CASES == *3* ]]; then
  clean_outputs
  cp "$ROOT/env.initial" .lake/paperlean/env.json
  capture env PAPERLEAN_MIDBUILD=0 PAPERLEAN_SCHEDULE_SLOTS=1 lake paperlean build Root PA
  keep_ref "$ROOT/ref3" pa/.lake/build ws/.lake/build
  clean_outputs
  cp "$ROOT/env.initial" .lake/paperlean/env.json
  G="$ROOT/gate3"; R="$ROOT/gate3r"; rm -rf "$G" "$R"; mkdir -p "$G" "$R"
  # (the root's task is dispatched, and held, before pa's; pa's task asks for ownership at once; the
  # root's resume is not held)
  GO "$G/start-pa"; GO "$G/resume-root"
  PAPERLEAN_MIDBUILD=1 PAPERLEAN_MIDBUILD_MIN=2 PAPERLEAN_MIDBUILD_DIV=2 PAPERLEAN_SCHEDULE_SLOTS=1 \
    PAPERLEAN_MIDBUILD_START_GATE="$G" PAPERLEAN_MIDBUILD_RESUME_GATE="$G" PAPERLEAN_MIDBUILD_RELOAD_GATE="$R" \
    lake paperlean build Root PA > "$ROOT/build3.log" 2>&1 &
  BUILD=$!
  abort3() { GO "$R/claimed"; GO "$G/start-root"; GO "$G/resume-pa"; stop $BUILD; cat "$ROOT/build3.log"; fail "(3) $1"; }
  wait_for 240 test -f "$R/claimed" || abort3 "pa's writer did not reach the reload gate"
  [ -f "$G/start-root" ] || abort3 "the root's preparation task was not dispatched before pa's preparation"
  GO "$R/claimed"
  wait_for 240 test -f "$G/resume-pa" || abort3 "pa's preparation did not reach the end of its pause"
  # (pa's writer has ended, pa is packed; its coordinator has not resumed the scheduler yet; pa's later
  # modules must still be pending, or a lifted pause could not be seen)
  compiled > "$ROOT/at-window"
  ! grep -q "/PA.olean$" "$ROOT/at-window" || abort3 "nothing of pa was left to compile at the end of its pause"
  rm -f "$R/claimed" "$R/claimed.go"
  GO "$G/start-root"
  # (time for the root's task to take ownership, pause, prepare and reach its writer's gate, if it could)
  early=0
  wait_for 30 test -f "$R/claimed" && early=1
  GO "$G/resume-pa"
  # the root may prepare later, legitimately: its pause must then hold while its writer is held
  held=none
  if wait_for 60 test -f "$R/claimed"; then
    compiled > "$ROOT/at-hold"
    sleep 4
    compiled > "$ROOT/at-hold2"
    # (`cmp`, not util.sh's `$DIFF` with `-q`: BSD diff rejects `-q` with its `-u` and would read as "lifted")
    held=ok; cmp -s -- "$ROOT/at-hold" "$ROOT/at-hold2" || held=lifted
    GO "$R/claimed"
  fi
  finish $BUILD "$ROOT/build3.log" "(3)"
  [ "$early" = 0 ] || fail "(3) the root's preparation took ownership before pa's coordinator had resumed the scheduler"
  [ "$held" != lifted ] || fail "(3) compiles went on while a preparation's writer was held (its pause was lifted)"
  grep -q "mid-build prepared pa" "$ROOT/build3.log" || fail "(3) pa's preparation was not given to the build"
  same_outputs "(3)" "$ROOT/ref3" pa/.lake/build ws/.lake/build
fi
true
