# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests the lock of the prepared data (`.lake/paperlean-lock.paperlean`) that cannot be opened, as it
# is a directory, a FIFO or has no permissions, or the project is read-only: `paperlean build` builds as
# `lake build` does, saying so, and without writing anything of its own; the commands that change the
# data refuse, naming the file. A `.lake` that only takes no new files does not stop a `paperlean build`
# from saying what it said elsewhere, or that it cannot.

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
check_out_contains "Prepared"
LOCK=.lake/paperlean-lock.paperlean
# (with a limit: a FIFO must not hang the commands)
limit="timeout 60"
n=1
check_lock() {
  n=$((n + 1))
  echo "def p : Nat := $n" > P.lean
  capture $limit lake paperlean build
  check_out_contains "PaperLean prepared data: not used: $WS/$LOCK cannot be opened"
  check_out_contains "building as \`lake build\` does"
  ! grep -q "paperlean: compiled" "$CAPTURED.out.produced" || fail "the build was accelerated"
  [ -z "$(ls .lake/paperlean-reuse-* .lake/paperlean-warnings-* 2> /dev/null)" ] ||
    fail "the build wrote PaperLean's files: $(ls .lake)"
  # (what the build compiled)
  capture lake env lean --stdin <<< "import P
#eval p"
  check_out_contains "$n"
  for cmd in "prepare p --no-native" "clean" "clean p"; do
    capture_fail $limit lake paperlean $cmd
    check_out_contains "cannot open $WS/$LOCK"
    check_out_contains "Nothing was changed"
    [ -f .lake/paperlean/env.json ] || fail "paperlean $cmd deleted the data"
  done
}

# a directory
rm -f "$LOCK"
mkdir "$LOCK"
check_lock
rmdir "$LOCK"

# no permissions
touch "$LOCK"
chmod 000 "$LOCK"
check_lock
chmod 644 "$LOCK"

# a FIFO
rm "$LOCK"
mkfifo "$LOCK"
check_lock
rm "$LOCK"

# A project that is read-only and up to date, as a shared checkout: like `lake build`.
echo 'def p : Nat := 100' > P.lean
capture lake paperlean build
check_out_contains "PaperLean prepared data: used"
trap 'chmod -R u+w "$TMP_DIR"; rm -rf "$TMP_DIR"' EXIT
chmod -R a-w "$WS"
capture lake build
capture lake paperlean build
check_out_contains "PaperLean prepared data: not used: $WS/$LOCK cannot be opened"
chmod -R u+w "$WS"
# (which gave the pack another identity, so that `lean` ignores it, as the build must say)
capture lake paperlean build
check_out_contains "it changed since it was written; run \`paperlean prepare\`"
capture lake paperlean prepare p --no-native

# Only `.lake` is read-only, and the lock can be opened: the files of a `paperlean` run are not needed.
chmod a-w .lake
capture lake paperlean build
check_out_contains "PaperLean prepared data: used"
chmod u+w .lake

# ... and a compile there is told as much as anywhere, with a dependency that runs in the interpreter:
# what its `lean` processes write goes to the build directory, and does not stay.
mkdir -p "$TMP_DIR/ro/dep"
cd "$TMP_DIR/ro"
cat > dep/lakefile.toml <<'END'
name = "rodep"
defaultTargets = ["Dep"]
[[lean_lib]]
name = "Dep"
END
printf 'builtin_initialize depRef : IO.Ref Nat ← IO.mkRef 0\ndef dep : Nat := 1\n' > dep/Dep.lean
cat > lakefile.toml <<'END'
name = "ro"
defaultTargets = ["R"]
[[require]]
name = "rodep"
path = "dep"
[[lean_lib]]
name = "R"
END
echo 'import Dep' > R.lean
run lake update
run lake build
capture lake paperlean prepare
check_compile() { # <what `paperlean build` must say of `Dep`, after the line for its kind>
  echo "-- changed" >> R.lean
  capture lake paperlean build
  check_out_contains "PaperLean prepared data: used"
  check_out_contains "paperlean: compiled 1 module(s)"
  check_out_contains "paperlean: 1 dependency module(s) run in the interpreter$1"
  check_out_contains "  Dep: $2"
}
builtin="it has \`builtin_initialize\` declarations"
check_compile ", with the same results but slower:" "$builtin"
trap 'chmod -R u+rwx "$TMP_DIR"; rm -rf "$TMP_DIR"' EXIT
chmod a-w .lake
check_compile ", with the same results but slower:" "$builtin"
[ -z "$(ls .lake/build/paperlean-* 2> /dev/null)" ] || fail "a file of the build stayed: $(ls .lake/build)"
# (and if its entries cannot be listed)
chmod 311 .lake
check_compile ", with the same results but slower:" "$builtin"
chmod 755 .lake
# Warnings of the `lean` processes are not lost there either, and name the file that holds them.
lib=$(ls "$PAPERLEAN_CACHE_DIR"/prepared/*/native/*/*.so "$PAPERLEAN_CACHE_DIR"/prepared/*/native/*/*.dylib 2> /dev/null || true)
chmod u+w "$lib"
printf 'x' >> "$lib"
chmod a-w .lake
check_compile " in some imports:" "its library's code cannot be used in this import"
check_out_contains "paperlean: 1 warning(s) about the prepared data, in "
grep -q "its library changed" .lake/build/paperlean-warnings-* || fail "the warning is not in the file that it names"
rm .lake/build/paperlean-warnings-*
# Nowhere to write: the build goes on, the warning is not lost, and the build says that nothing is known,
# not that nothing happened.
chmod a-w .lake/build
echo "-- changed" >> R.lean
capture lake paperlean build
check_out_contains "Build completed successfully"
check_out_contains "its library changed"
check_out_contains "paperlean: no summary of what was not accelerated: no file can be written for it"
chmod 755 .lake .lake/build
