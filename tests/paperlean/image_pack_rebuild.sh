# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that `paperlean prepare` writes the import image again when a pack that the image describes
# was written again under the same name: here the dependency's build directory, the cache and the data
# directory are each replaced by a copy (same bytes, other identities, as after restoring a backup), so
# that `prepare` finds the pack entry unusable and packs again, with the files' new identities.
# The image records the checksum and address range of each pack, and `lean` ignores an image of other
# packs ("it belongs to other olean packs"), importing without it. `paperlean status` must not report
# such an image as used.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN
ROOT="$(cd "$TMP_DIR" && pwd -P)"
CACHE="$PAPERLEAN_CACHE_DIR/prepared"
mkdir -p "$ROOT/ws/dep/Dep"
cd "$ROOT/ws"
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
run lake paperlean prepare -j 2
check_image_used() {  # <step>
  capture env PAPERLEAN_ACCELERATE=1 lake lean Root.lean
  check_out_contains "42"
  if grep -q 'ignoring import image' "$CAPTURED.out.produced"; then
    fail "$1: lean ignores the import image: $(grep 'import image' "$CAPTURED.out.produced")"
  fi
  capture lake paperlean status
  check_out_contains "an import image"
}
check_image_used "first prepare"
recopy() { cp -pR "$1" "$1.copy" && rm -rf "$1" && mv "$1.copy" "$1" || fail "cannot copy $1"; }
recopy "$ROOT/ws/dep/.lake"
recopy "$PAPERLEAN_CACHE_DIR"
recopy "$ROOT/ws/.lake/paperlean"
run lake paperlean prepare -j 2
check_image_used "prepare after the copies"
