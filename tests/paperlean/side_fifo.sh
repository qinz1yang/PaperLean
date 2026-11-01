# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that a FIFO in place of a side file does not hang the `paperlean` commands, on which opening
# a file would wait for ever: `env.json` counts as damaged, and the records of a build are ignored.
# Each command runs under a limit.

export XDG_CACHE_HOME="$(cd "$TMP_DIR" && pwd -P)/cache"
WS="$(cd "$TMP_DIR" && pwd -P)/ws"
mkdir -p "$WS"
cd "$WS"
cat > lakefile.toml <<'END'
name = "p"
defaultTargets = ["P"]
[[lean_lib]]
name = "P"
END
echo 'def p : Nat := 1' > P.lean
run lake build
capture lake paperlean prepare p --no-native
limit="timeout 60"
n=1
edit() { n=$((n + 1)); echo "def p : Nat := $n" > P.lean; }

# `env.json`
fifo_env() { rm -rf .lake/paperlean/env.json; mkfifo .lake/paperlean/env.json; }
fifo_env
edit
capture $limit lake paperlean build
check_out_contains "PaperLean prepared data: not used"
check_out_contains "is damaged: it is not a regular file"
capture $limit lake paperlean status
check_out_contains "is damaged: it is not a regular file"
edit
capture $limit env PAPERLEAN_ACCELERATE=1 lake build
capture $limit lake paperlean clean p
capture $limit lake paperlean prepare p --no-native
check_out_contains "Prepared"
[ -f .lake/paperlean/env.json ] || fail "prepare left the FIFO"
fifo_env
capture $limit lake paperlean clean
[ ! -e .lake/paperlean ] || fail "clean left the data"
capture lake paperlean prepare p --no-native

# the records of a build
for f in paperlean-times.paperlean paperlean-hashes.paperlean paperlean-clock.paperlean; do
  rm -f .lake/$f
  mkfifo .lake/$f
  edit
  capture $limit lake paperlean build
  check_out_contains "PaperLean prepared data: used"
  rm -f .lake/$f
  mkfifo .lake/$f
  edit
  capture $limit env PAPERLEAN_ACCELERATE=1 lake build
  rm -f .lake/$f
done
