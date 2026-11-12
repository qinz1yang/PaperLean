# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# `relPathFrom` and `LeanLib.findModuleBySrc?` must require a complete path
# component, not a string prefix.  A sibling directory whose name starts with
# the root's name must not lose its first character, and a path outside a
# library's source directory must not resolve to a module that happens to have
# the same relative suffix.

WS="$TMP_DIR/lake-relpath"
mkdir -p "$WS"
cd "$WS"
cat > Main.lean <<'LEAN'
import Lake.Util.FilePath

open System Lake

def check (root path expected : String) : IO Bool := do
  let got := (relPathFrom root path).toString
  if got = expected then
    return true
  else
    IO.eprintln s!"relPathFrom {repr root} {repr path}: expected {repr expected}, got {repr got}"
    return false

def main : IO Unit := do
  let cases : List (String × String × String) := [
    ("/a/b", "/a/b/d", "d"),
    -- A sibling whose name starts with the root name is not under the root.
    ("/a/b", "/a/bc/d", "/a/bc/d"),
    -- The root itself is a path component.
    ("/", "/a", "a"),
    -- A trailing separator in the root must not eat the first component.
    ("/a/b/", "/a/b/c", "c"),
    -- The root itself keeps the historical empty result.
    ("/a/b", "/a/b", ""),
    -- A non-normalized path that is not under the root is returned verbatim.
    ("/a/b", "/a/bc/../x", "/a/bc/../x")
  ]
  let mut ok := true
  for (root, path, expected) in cases do
    ok := (← check root path expected) && ok
  unless ok do
    IO.Process.exit 1
LEAN
run lean --run Main.lean

# Package-level check for `LeanLib.findModuleBySrc?`.
mkdir -p lib/extra lib-extra
cat > lakefile.toml <<'TOML'
name = "p"

[[lean_lib]]
name = "Lib"
srcDir = "lib"
roots = ["extra.Foo"]
TOML
printf 'def x : Nat := 1\n' > lib/extra/Foo.lean
# This is a sibling of the library's srcDir, not a module of the library.
printf 'def y : Nat := 2\n' > lib-extra/Foo.lean
capture_fail lake build "$WS/lib-extra/Foo.lean"
[ ! -e .lake/build/lib/lean/extra/Foo.olean ] || fail "the unrelated extra.Foo module was built"
true
