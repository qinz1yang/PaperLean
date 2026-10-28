# Tests `paperlean prepare` and `paperlean clean` of named packages (`Lake.PaperLean.Prepare`): a name
# is a package's or a library's (exact, else in any case); preparing a package adds it and the
# packages it depends on that are not prepared yet, builds the native libraries of the named packages
# and of those that depend on them, and keeps the data of the other packages (their libraries are not
# compiled again and stay where they are, also when a library built now is linked against them);
# cleaning a package deletes its data and that of the prepared packages that depend on it.
# Workspace: root requires b (which requires a) and c (library Cee).

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN
WS="$(cd "$TMP_DIR" && pwd -P)/ws"
mkdir -p "$TMP_DIR/a" "$TMP_DIR/b" "$TMP_DIR/c" "$WS/Root"
lib() {  # <package dir> <name> <library> [required package]
  {
    echo "name = \"$2\""
    echo "defaultTargets = [\"$3\"]"
    if [ -n "${4:-}" ]; then printf '[[require]]\nname = "%s"\npath = "../%s"\n' "$4" "$4"; fi
    printf '[[lean_lib]]\nname = "%s"\n' "$3"
  } > "$1/lakefile.toml"
}
lib "$TMP_DIR/a" a A
lib "$TMP_DIR/b" b B a
lib "$TMP_DIR/c" c Cee
echo 'def aValue (n : Nat) : Nat := n + 1' > "$TMP_DIR/a/A.lean"
printf 'import A\ndef bValue (n : Nat) : Nat := aValue n * 2\n' > "$TMP_DIR/b/B.lean"
echo 'def cValue (n : Nat) : Nat := n + 10' > "$TMP_DIR/c/Cee.lean"
cat > "$WS/lakefile.toml" <<'EOF'
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "b"
path = "../b"
[[require]]
name = "c"
path = "../c"
[[lean_lib]]
name = "Root"
EOF
echo 'import Root.Main' > "$WS/Root.lean"
printf 'import B\nimport Cee\n#eval bValue 2 + cValue 1\n' > "$WS/Root/Main.lean"
cd "$WS"
run lake build

# The prepared packages; the native library of a package in `env.json`; how many libraries an import
# of the root's module uses; whether the last command compiled a package's library.
status_of() {
  capture lake paperlean status
  check_out_contains "package a: $1"; check_out_contains "package b: $2"; check_out_contains "package c: $3"
}
lib_of() { grep -o "\"native-[0-9]*/$1\.[a-z]*\"" .lake/paperlean/env.json | grep -v paperlean || true; }
native_used() {
  capture env PAPERLEAN_IMPORT_TIMING=1 PAPERLEAN_ACCELERATE=1 lake lean Root/Main.lean
  check_out_contains "17"
  if [ "$1" = 0 ]; then
    ! grep -q "paperlean-timing native libs=[1-9]" "$CAPTURED.out.produced" || fail "native libraries were used"
  else
    check_out_matches "paperlean-timing native libs=$1 "
  fi
}
compiled() { grep -Fq "Compiling the native library of $1 " "$CAPTURED.out.produced"; }

# A library's name names its package: b, with a, which it depends on, but not c.
capture lake paperlean prepare B
check_out_contains "Prepared"
compiled a || fail "prepare B did not compile a's library"
compiled b || fail "prepare B did not compile b's library"
compiled c && fail "prepare B compiled c's library"
status_of prepared prepared "not prepared"
native_used 2

# Preparing c (its library's name in another case) adds it and keeps the data of a and b: their
# libraries are not compiled again and stay where they are.
LIB_A=$(lib_of a); LIB_B=$(lib_of b)
[ -n "$LIB_A" ] && [ -n "$LIB_B" ] || fail "no libraries of a and b in env.json"
capture lake paperlean prepare cee
compiled c || fail "prepare cee did not compile c's library"
compiled a && fail "prepare cee compiled a's library"
compiled b && fail "prepare cee compiled b's library"
[ "$(lib_of a)" = "$LIB_A" ] && [ "$(lib_of b)" = "$LIB_B" ] || fail "prepare cee moved the libraries of a or b"
[ -f ".lake/paperlean/$(echo $LIB_A | tr -d '"')" ] || fail "a's library is gone"
status_of prepared prepared prepared
native_used 3

# Preparing b again compiles only b's library, linked against a's, which stays in the directory of
# an earlier run; c keeps its data.
LIB_C=$(lib_of c)
capture lake paperlean prepare b
compiled b || fail "prepare b did not compile b's library"
compiled a && fail "prepare b compiled a's library"
compiled c && fail "prepare b compiled c's library"
[ "$(lib_of a)" = "$LIB_A" ] && [ "$(lib_of c)" = "$LIB_C" ] || fail "prepare b moved the libraries of a or c"
[ "$(lib_of b)" != "$LIB_B" ] || fail "prepare b did not write b's library anew"
native_used 3

# Preparing a again compiles a's library and b's, which depends on it; c keeps its data.
capture lake paperlean prepare A
compiled a || fail "prepare A did not compile a's library"
compiled b || fail "prepare A did not compile b's library"
compiled c && fail "prepare A compiled c's library"
[ "$(lib_of c)" = "$LIB_C" ] || fail "prepare A moved c's library"
native_used 3

# Everything prepared: naming the root packs it, and nothing of the dependencies changes.
LIBS=$(lib_of '[abc]')
capture lake paperlean prepare root
check_out_contains "of root"
compiled a && fail "prepare root compiled a's library"
[ "$(lib_of '[abc]')" = "$LIBS" ] || fail "prepare root changed the dependencies' libraries"

# Cleaning a deletes the data of a and of b, which depends on it; c keeps its data, and the root its pack.
capture lake paperlean clean a
check_out_contains "Deleted the prepared data of a, b"
status_of "not prepared" "not prepared" prepared
[ "$(lib_of c)" = "$LIB_C" ] || fail "clean a moved c's library"
[ -n "$(lib_of a)$(lib_of b)" ] && fail "clean a kept a library of a or b"
grep -q '"root-[0-9]*/root.paperlean"' .lake/paperlean/env.json || fail "clean a deleted the root's pack"
native_used 1
capture lake paperlean clean c
check_out_contains "Deleted the prepared data of c"
status_of "not prepared" "not prepared" "not prepared"
ls -d .lake/paperlean/deps-* .lake/paperlean/native-* 2> /dev/null && fail "clean c kept files of the dependencies"
native_used 0
capture lake paperlean clean c
check_out_contains "c: not prepared; nothing was deleted"

# A name that matches nothing changes nothing; one that matches several packages lists them.
capture_exit 1 lake paperlean prepare d
check_out_contains "there is no package or library 'd'"
echo '[[lean_lib]]
name = "c"' >> "$TMP_DIR/a/lakefile.toml"
capture_exit 1 lake paperlean prepare c
check_out_contains "'c' matches several packages: "
check_out_contains "package c"
check_out_contains "library c of a"
check_out_contains "Nothing was changed"
