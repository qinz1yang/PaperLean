# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests what `reuse_suite.py` reports, with a `lean` in front of the real one that changes chosen runs
# with the oracle (numbered in order): that an oracle finding fails the run, with its diagnostic, in
# the first run and in a repeat alone, however clean the other repeats are; that so does a run with
# reuse that a signal ends, in the first run and in a repeat alone; that a difference that does not
# repeat, as of a limit of time under load, does not, and is reported also if only a repeat shows it;
# and that what is left out of the messages is Lean's and the measurements' lines of times
# alone, so that the statement of a theorem with a numeral before a variable `s` stays compared, as do
# the messages of a file that prints times, and no expected output of the suite changes.
SUITE="$(dirname "$FILE")/reuse_suite.py"
REAL="$(command -v lean)"
cd "$TMP_DIR"
mkdir bin
cat > bin/lean <<EOF2
#!/usr/bin/env bash
[ -n "\${PAPERLEAN_REUSE_ORACLE:-}" ] || exec "$REAL" "\$@"
n=\$((\$(cat "$TMP_DIR/count") + 1))
echo \$n > "$TMP_DIR/count"
case \$FAULT_CASE:\$n in
  first:1 | retry:2) PAPERLEAN_REUSE_FAULT=tc-names exec "$REAL" "\$@";;
  retry:1 | noise:1 | retrysignal:1 | retryexit:1)
    "$REAL" "\$@"; r=\$?; echo "a line that this run alone prints"; exit \$r;;
  signal:1 | retrysignal:2) kill -KILL \$\$;;
  retryexit:2) "$REAL" "\$@"; exit 7;;
esac
case \$FAULT_CASE:\${@: -1} in
  math:streamEqIssue.lean)
    "$REAL" "\$@" | sed 's/hasLength 0 s = true/hasLength 1 s = false/'; exit \${PIPESTATUS[0]};;
  timed:646.lean) "$REAL" "\$@"; r=\$?; echo "a message that only reuse prints"; exit \$r;;
esac
exec "$REAL" "\$@"
EOF2
chmod +x bin/lean

# Runs the suite on some files with the changes of case `$1`: `1193a.lean` reuses results, so that its
# exit code is that of what it reports, and `646.lean` prints a time. Sets `$r` to its exit code.
suite() {
  echo 0 > count
  r=0
  FAULT_CASE=$1 PATH="$TMP_DIR/bin:$PATH" python3 "$SUITE" -j1 --out "$1.jsonl" \
    --files 1193a.lean,646.lean,streamEqIssue.lean elab > "$1.log" 2>&1 || r=$?
}
diagnostic="PaperLean: the reuse oracle found a difference: typeclass cache: Lean's search takes"

suite clean
[ $r = 0 ] || fail "the suite fails with no change: $(cat clean.log)"
! grep -Eq "^(ORACLE|DIFFERS|TRANSIENT) " clean.log || fail "the suite reports with no change: $(cat clean.log)"

# In the first run with the oracle, the repeats clean.
suite first
[ "$(cat count)" -ge 4 ] || fail "the suite did not repeat the run: $(cat first.log)"
[ $r = 1 ] || fail "an oracle finding of the first run passed: $(cat first.log)"
grep -q "^ORACLE elab/1193a.lean" first.log || fail "the first run's finding is not named: $(cat first.log)"
grep -q "$diagnostic" first.log || fail "the diagnostic of the first run is lost: $(cat first.log)"
grep -q "$diagnostic" first.jsonl || fail "the log lost the diagnostic: $(cat first.jsonl)"

# In a repeat alone: the first run differs, as under load, and finds nothing.
suite retry
[ $r = 1 ] || fail "an oracle finding of a repeat passed: $(cat retry.log)"
grep -q "^ORACLE elab/1193a.lean" retry.log || fail "the repeat's finding is not named: $(cat retry.log)"
grep -q "$diagnostic" retry.log || fail "the diagnostic of the repeat is lost: $(cat retry.log)"

# A signal is no matter of time either ...
suite signal
[ $r = 1 ] || fail "a run that a signal ended passed: $(cat signal.log)"
grep -q "^SIGNAL elab/1193a.lean .*signal 9" signal.log || fail "the signal is not reported: $(cat signal.log)"

# ... in a repeat alone too, where the first run differs only in a message.
suite retrysignal
[ $r = 1 ] || fail "a repeat that a signal ended passed: $(cat retrysignal.log)"
grep -q "^SIGNAL elab/1193a.lean .*signal 9" retrysignal.log ||
  fail "the signal of the repeat is not reported: $(cat retrysignal.log)"
grep -q '"signals": \[-9\]' retrysignal.jsonl || fail "the log lost the signal: $(cat retrysignal.jsonl)"

# What does not repeat and finds nothing stays transient: repeats are there for that.
suite noise
[ $r = 0 ] || fail "a difference of one run under load failed: $(cat noise.log)"
grep -q "^TRANSIENT elab/1193a.lean" noise.log || fail "the difference is not reported: $(cat noise.log)"
! grep -q "^ORACLE " noise.log || fail "no oracle finding here: $(cat noise.log)"

# What only a repeat shows is reported: the first run differs only in a message, the second in its exit code.
suite retryexit
[ $r = 0 ] || fail "a difference of one run under load failed: $(cat retryexit.log)"
grep -q "^TRANSIENT elab/1193a.lean .*exit" retryexit.log || fail "the repeat's difference is lost: $(cat retryexit.log)"

# Another conclusion of a theorem: `hasLength 0 s = true` is no time.
suite math
[ $r = 1 ] || fail "another statement of a theorem passed: $(cat math.log)"
grep -q "^DIFFERS elab/streamEqIssue.lean .*output" math.log || fail "the statement is not reported: $(cat math.log)"

# A file that prints a time stays compared: the time does not make its messages vary.
suite timed
[ $r = 1 ] || fail "another message of a file that prints a time passed: $(cat timed.log)"
grep -q "^DIFFERS elab/646.lean .*output" timed.log || fail "the message is not reported: $(cat timed.log)"

# The same on the lines themselves, and the times that are left out: all that Lean prints of them.
cat > normalize.py <<EOF2
import glob
import importlib.util
spec = importlib.util.spec_from_file_location("reuse_suite", "$SUITE")
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
tests = "$(dirname "$FILE")/.."
# an expected output is the same in every run, so that none of it is a time
for pile in m.PILES:
    for path in glob.glob(f"{tests}/{pile}/*.out.expected"):
        text = open(path, "rb").read()
        assert m.normalize(text) == text, path
expected = open(f"{tests}/elab/streamEqIssue.lean.out.expected", "rb").read()
changed = expected.replace(b"hasLength 0 s = true", b"hasLength 1 s = false")
assert expected != changed
assert m.normalize(expected) == expected, "the output of a theorem was changed"
assert m.normalize(changed) == changed, "the output of a theorem was changed"
# what mathematics and messages may hold
for line in [b"f 0 s = g 1 s", b"x 2 ms = y", b"2 s", b"1.5s + 2ms", b"it took 3 s", b"took 3s more",
             b"measurement", b"measurement: a b c d", b"\t0 s", b"\ttypeclass inference 5ms", b"time 3 s",
             b"time: 3 s", b"time : 3ms", b"f time 3ms", b"goal_1: 2.5 ms", b"goal 1: 2.500000 s"]:
    assert m.normalize(line + b"\n") == line + b"\n", line
# what Lean's profiler prints (\`time_task.cpp\`, \`timeit.cpp\`), which comes and goes with its threshold
a = b"1\ninterpretation of f took 997ms\n2\nelaboration took 1.23s\n3\nlinting took 1e+03ms\n"
b = b"1\n2\ninterpretation of f took 5.05ms\n3\n"
assert m.normalize(a) == m.normalize(b) == b"1\n2\n3\n"
a = b"cumulative profiling times:\n\telaboration 12.3ms\n\tlinting 2s\nnext\n"
b = b"cumulative profiling times:\n\telaboration 9ms\nnext\n"
assert m.normalize(a) == m.normalize(b) == b"cumulative profiling times:\nnext\n"
# what \`time\` and \`timeit\` print, and the benchmarks with \`s!"{ms} ms"\` of a \`Float\`, whose names stay
for a, b in [(b"time: 1100ms\n", b"time: 9ms\n"), (b"time 2.49ms\n", b"time 5ms\n"),
             (b"cbv: goal_6: 114.532369 ms, kernel: 38.054479 ms\n", b"cbv: goal_6: 1.000000 ms, kernel: 2.000000 ms\n"),
             (b"decide: goal_6: 1.532369 ms, kernel: 8.054479 ms\n", b"decide: goal_6: 2.000000 ms, kernel: 1.000000 ms\n"),
             (b"mergeSort_10: cbv 77.613449 ms, kernel 9.447010 ms\n", b"mergeSort_10: cbv 1.000000 ms, kernel 2.000000 ms\n"),
             (b"pow2DoubleEq 5: cbv 7.613449 ms, kernel 9.447010 ms\n", b"pow2DoubleEq 5: cbv 1.000000 ms, kernel 2.000000 ms\n"),
             (b"goal_6: 1.910620 ms\n", b"goal_6: 2.000000 ms\n"), (b"mergeSort_1: 1.910620 ms (rfl)\n", b"mergeSort_1: 2.000000 ms (rfl)\n")]:
    assert m.normalize(a) == m.normalize(b), a
assert m.normalize(b"cbv: goal_6: 1.000000 ms, kernel: 2.000000 ms\n") != m.normalize(b"cbv: goal_7: 1.000000 ms, kernel: 2.000000 ms\n")
# measurements keep their names, as \`normalize_measurements\` of \`util.sh\` does
assert m.normalize(b"measurement: split_400 1.25 s\n") == b"measurement: split_400 ...\n"
assert m.normalize(b"measurement: count 12\n") == b"measurement: count ...\n"
assert m.normalize(b"measurement: a 1 s\n") != m.normalize(b"measurement: b 1 s\n")
EOF2
python3 -B normalize.py || fail "normalize.py"
