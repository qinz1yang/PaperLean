# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that every `paperlean` command treats an `env.json` of prepared data (`.lake/paperlean/`,
# `src/lake/Lake/PaperLean/Env.lean`) that cannot be read or decoded (not UTF-8 text, a directory, no
# read permission) as unusable optional data, like damaged JSON: `status` and `build` complete and say
# that it is not used; `prepare`, `build --prepare` and `clean` of a package, of the root package as of
# a dependency, replace it, the last under the lock of the data, with data that holds nothing and without
# deleting a pack; and `clean` deletes it.

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
cp -a .lake/paperlean "$TMP_DIR/data"
# the prepared data, with `env.json` damaged as $1 says
damaged() {
  [ ! -e .lake/paperlean ] || chmod -R u+rwX .lake/paperlean
  rm -rf .lake/paperlean
  cp -a "$TMP_DIR/data" .lake/paperlean
  case $1 in
    utf8) printf '\377\376\377' > .lake/paperlean/env.json ;;
    dir) rm .lake/paperlean/env.json; mkdir .lake/paperlean/env.json ;;
    unreadable) chmod 000 .lake/paperlean/env.json ;;
  esac
}
# what `clean` of a package leaves in the workspace of the current directory: an `env.json` that is
# usable at once, and holds nothing, and the pack $1 that the damaged one may have listed
recovered() {
  [ -f .lake/paperlean/env.json ] && [ -r .lake/paperlean/env.json ] || fail "clean of a package left no readable env.json"
  [ -f "$1" ] || fail "clean of a package deleted $1"
  capture lake paperlean status
  check_out_contains "none prepared: run \`paperlean prepare\`"
  ! grep -q "is damaged" "$CAPTURED.out.produced" || fail "the data is still damaged after clean of a package"
  capture lake paperlean status --verify
  check_out_contains "none prepared"
  capture lake paperlean build
  check_out_contains "PaperLean prepared data: none prepared"
}
PACK=.lake/paperlean/$(cd "$TMP_DIR/data" && ls -d root-*)/root.paperlean
# the workspace of `clean` of a dependency; its data is only damaged, so needs no real packs
WSD="$(cd "$TMP_DIR" && pwd -P)/wsd"
mkdir -p "$WSD/Dep" "$WSD/dep"
printf 'name = "dep"\ndefaultTargets = ["Dep"]\n[[lean_lib]]\nname = "Dep"\n' > "$WSD/dep/lakefile.toml"
echo 'def d : Nat := 1' > "$WSD/dep/Dep.lean"
printf 'name = "r"\ndefaultTargets = ["R"]\n[[require]]\nname = "dep"\npath = "dep"\n[[lean_lib]]\nname = "R"\n' > "$WSD/lakefile.toml"
printf 'import Dep\ndef r : Nat := d\n' > "$WSD/R.lean"
for kind in utf8 dir unreadable; do
  damaged $kind
  # (a superuser reads it all the same)
  if [ $kind = unreadable ] && [ -r .lake/paperlean/env.json ]; then continue; fi
  capture lake paperlean status
  check_out_contains "prepared data ($WS/.lake/paperlean): not used: $WS/.lake/paperlean/env.json is damaged"
  capture lake paperlean status --verify
  check_out_contains "not used: $WS/.lake/paperlean/env.json is damaged"
  capture lake paperlean build
  check_out_contains "PaperLean prepared data: not used"
  capture lake paperlean clean p
  check_out_contains "It is reset"
  recovered "$PACK"
  capture lake paperlean clean p
  check_out_contains "Deleted the pack of p"
  damaged $kind
  capture lake paperlean prepare p --no-native
  check_out_contains "Prepared"
  capture lake paperlean status
  check_out_contains "used: 1 pack(s)"
  [ ! -e "$PACK" ] || fail "prepare kept the pack that the damaged env.json may have listed"
  (
    cd "$WSD"
    rm -rf .lake/paperlean
    mkdir -p .lake/paperlean/deps-1
    echo pack > .lake/paperlean/deps-1/deps.paperlean
    case $kind in
      utf8) printf '\377\376\377' > .lake/paperlean/env.json ;;
      dir) mkdir .lake/paperlean/env.json ;;
      unreadable) echo '{}' > .lake/paperlean/env.json; chmod 000 .lake/paperlean/env.json ;;
    esac
    capture lake paperlean clean dep
    check_out_contains "It is reset"
    recovered .lake/paperlean/deps-1/deps.paperlean
    capture lake paperlean clean dep
    check_out_contains "dep: not prepared; nothing was deleted."
    capture lake paperlean clean r dep
    check_out_contains "dep: not prepared; nothing was deleted."
    capture lake paperlean status
    check_out_contains "package dep: not prepared"
  )
  damaged $kind
  capture lake paperlean build --prepare
  check_out_contains "The prepared data cannot be used"
  capture lake paperlean status
  check_out_contains "used: 1 pack(s)"
  damaged $kind
  capture lake paperlean clean
  [ ! -e .lake/paperlean ] || fail "clean left the data"
done

# `clean` of a package resets `env.json` only under the lock of the data: while another process holds
# it, `clean` refuses and changes nothing, for the root package as for a dependency.
if command -v flock > /dev/null; then
  check_locked() { # package
    printf '\377\376\377' > .lake/paperlean/env.json
    exec 9>> .lake/paperlean-lock.paperlean
    flock -x 9
    capture_exit 1 lake paperlean clean $1
    check_out_contains "another paperlean command is changing the prepared data"
    exec 9>&-
    cmp -s .lake/paperlean/env.json <(printf '\377\376\377') || fail "clean of $1 changed env.json without the lock"
  }
  capture lake paperlean prepare p --no-native
  check_locked p
  (cd "$WSD"; check_locked dep)
fi

# Recovery ends in real data again: `prepare` uses what `clean` of a package left, and deletes the
# packs that are no longer listed.
cd "$WSD"
capture lake paperlean prepare --no-native
check_out_contains "Prepared"
capture lake paperlean status
check_out_contains "used: 1 pack(s)"
[ ! -e .lake/paperlean/deps-1 ] || fail "prepare kept the pack that the damaged env.json may have listed"
