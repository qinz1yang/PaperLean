# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that a damaged side file of a module's setup (`<module>.setup.paperlean`) does not stop
# `paperlean build`, as nothing stops `lake build`: a directory, a FIFO, on which a write would wait for
# ever, a link to either, a file that cannot be written and a directory that cannot be deleted, where
# the build falls back to the conventional setup file. Each build gives what `lake build` gives, for a
# non-module file and for a `module`, whose IR `leanir` compiles from the same setup. Each command runs
# under a limit.

export XDG_CACHE_HOME="$(cd "$TMP_DIR" && pwd -P)/cache"
export PAPERLEAN_BUILD_PACKS=0
WS="$(cd "$TMP_DIR" && pwd -P)/ws"
mkdir -p "$WS"
cd "$WS"
cat > lakefile.toml <<'END'
name = "p"
defaultTargets = ["P", "Q"]
[[lean_lib]]
name = "P"
[[lean_lib]]
name = "Q"
END
trap 'chmod -R u+rwx "$TMP_DIR"; rm -rf "$TMP_DIR"' EXIT
limit="timeout 60"
IR=.lake/build/ir
source_of() {
  echo "def p : Nat := $1" > P.lean
  printf 'module\npublic def q : Nat := %s\n' "$1" > Q.lean
}
# what `lake build` gives for the value `$1`
expected() {
  mkdir -p "$TMP_DIR/expected/$1"
  source_of "$1"
  run lake build
  for f in P.c Q.c; do cp "$IR/$f" "$TMP_DIR/expected/$1/"; done
  rm -rf .lake/build
}
# `paperlean build` of the value `$1` gives the declarations and the code of `lake build`.
check_build() {
  source_of "$1"
  capture $limit lake paperlean build
  for f in P.c Q.c; do
    cmp "$IR/$f" "$TMP_DIR/expected/$1/$f" || fail "$f is not what lake build compiles"
  done
  capture lake env lean --stdin <<< "import P
import Q
#eval (p, q)
#print axioms p"
  check_out_contains "($1, $1)"
  check_out_contains "'p' does not depend on any axioms"
}
# the damage `$2`, a shell command, at the side files of both modules, for the value `$1`
check_damage() {
  rm -rf .lake/build
  mkdir -p "$IR"
  for m in P Q; do side="$IR/$m.setup.paperlean" eval "$2"; done
  check_build "$1"
}
compact() { # the side file `$1` was written, with the compact form
  [ -f "$1" ] && [ ! -L "$1" ] || fail "$1 is not a regular file"
}

expected 1
expected 2
expected 3
expected 4
expected 5
expected 6
expected 7
expected 8

# undamaged
check_build 1
for m in P Q; do compact "$IR/$m.setup.paperlean"; done
[ ! -e "$IR/P.setup.json" ] || fail "paperlean build wrote the conventional setup file"
# a directory, empty or not
check_damage 2 'mkdir "$side"'
for m in P Q; do compact "$IR/$m.setup.paperlean"; done
check_damage 3 'mkdir -p "$side/sub"; echo x > "$side/sub/f"'
for m in P Q; do compact "$IR/$m.setup.paperlean"; done
# a FIFO
check_damage 4 'mkfifo "$side"'
for m in P Q; do compact "$IR/$m.setup.paperlean"; done
# links to a FIFO and to a directory
mkfifo "$TMP_DIR/fifo"
check_damage 5 'ln -s "$TMP_DIR/fifo" "$side"'
for m in P Q; do compact "$IR/$m.setup.paperlean"; done
check_damage 6 'ln -s "$TMP_DIR" "$side"'
for m in P Q; do compact "$IR/$m.setup.paperlean"; done
# a file without permissions
check_damage 7 'echo x > "$side"; chmod 000 "$side"'
for m in P Q; do compact "$IR/$m.setup.paperlean"; done
# what cannot be replaced: the conventional setup file is written
check_damage 8 'mkdir -p "$side/sub"; echo x > "$side/sub/f"; chmod a-w "$side/sub"'
for m in P Q; do
  [ -d "$IR/$m.setup.paperlean" ] || fail "the test does not test this: $m's side file was replaced"
  grep -q '"importArts"' "$IR/$m.setup.json" || fail "$m.setup.json was not written"
done
