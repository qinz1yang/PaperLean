# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests `paperlean clean --cache`: it deletes the entries of the cache that the prepared data of no
# workspace that used the cache lists (and, with `--unused-for DAYS`, only those not used in that
# time), and keeps the others, which their workspaces go on using. `paperlean clean` of a workspace
# leaves the cache to it.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN
ROOT="$(cd "$TMP_DIR" && pwd -P)"
CACHE="$PAPERLEAN_CACHE_DIR/prepared"
mkdir -p "$ROOT/ws1/dep/Dep"
cd "$ROOT/ws1"
cat > dep/lakefile.toml <<'END'
name = "dep"
defaultTargets = ["Dep"]
[[lean_lib]]
name = "Dep"
END
printf 'def base (n : Nat) : Nat := n + 1\n' > dep/Dep/Base.lean
printf 'import Dep.Base\n' > dep/Dep.lean
cat > lakefile.toml <<'END'
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "dep"
path = "dep"
[[lean_lib]]
name = "Root"
END
printf 'import Dep\n#eval base 41\n' > Root.lean
run lake build Dep
cp -pR "$ROOT/ws1" "$ROOT/ws2"
run lake paperlean prepare -j 2
# ws2 then has another version of dep.
cd "$ROOT/ws2"
printf 'def base (n : Nat) : Nat := n + 2\n' > dep/Dep/Base.lean
run lake build Dep
run lake paperlean prepare -j 2
packs() { ls -d "$CACHE"/*/pack/dep-* 2> /dev/null | wc -l | tr -d ' '; }
libs() { ls -d "$CACHE"/*/native/dep-* 2> /dev/null | wc -l | tr -d ' '; }
[ "$(packs)" = 2 ] && [ "$(libs)" = 2 ] || fail "not two versions of dep in the cache: $(packs), $(libs)"
check_use() {  # <workspace> <output>
  (cd "$ROOT/$1" && capture env PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean Root.lean &&
    check_out_matches "paperlean-timing native libs=1 " && check_out_contains "$2")
}

# Both are in use.
capture lake paperlean clean --cache
check_out_contains "Deleted 0 entries"
[ "$(packs)" = 2 ] && [ "$(libs)" = 2 ] || fail "clean --cache deleted entries in use"
check_use ws1 42
check_use ws2 43

# ws1 deletes its prepared data; its entries are deleted once unused for the time asked for.
(cd "$ROOT/ws1" && run lake paperlean clean)
[ "$(packs)" = 2 ] || fail "clean of a workspace deleted entries of the cache"
capture lake paperlean clean --cache --unused-for 1
check_out_contains "Deleted 0 entries"
[ "$(packs)" = 2 ] || fail "clean --cache --unused-for 1 deleted an entry used today"
capture lake paperlean clean --cache
check_out_contains "Deleted 2 entries"
[ "$(packs)" = 1 ] && [ "$(libs)" = 1 ] || fail "clean --cache did not delete ws1's entries: $(packs), $(libs)"
check_use ws2 43

# A workspace that no longer exists keeps nothing.
cd "$ROOT/ws1"
rm -rf "$ROOT/ws2"
capture lake paperlean clean --cache
check_out_contains "Deleted 2 entries"
[ "$(packs)" = 0 ] && [ "$(libs)" = 0 ] || fail "entries of a deleted workspace were kept"
