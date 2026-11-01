# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that `SearchPath.findWithExt` looks a package up in the search path on every call, as official
# Lean does: once an earlier entry gains a package that a later entry has, it finds the earlier one,
# in the lookup itself and in what an elaborator makes of it (an environment that depends on the file
# system must be official Lean's, also under `PAPERLEAN_EXACT=1`).
cd "$TMP_DIR"

cat > Lookup.lean <<'LEAN'
import Lean
open Lean

#eval show IO Unit from do
  let d ← IO.FS.createTempDir
  let a := d / "a"
  let b := d / "b"
  IO.FS.createDirAll (b / "Foo")
  IO.FS.createDirAll a
  let sp : SearchPath := [a, b]
  let shown (r : Option System.FilePath) := (r.map (·.toString.replace d.toString "")).getD "none"
  IO.println s!"before: {shown (← sp.findWithExt "olean" `Foo.Bar)}"
  IO.FS.createDirAll (a / "Foo")
  IO.println s!"after: {shown (← sp.findWithExt "olean" `Foo.Bar)}"
  IO.FS.removeDirAll (a / "Foo")
  IO.println s!"removed: {shown (← sp.findWithExt "olean" `Foo.Bar)}"
  IO.FS.writeFile (a / "Foo.olean") ""
  IO.println s!"file: {shown (← sp.findWithExt "olean" `Foo.Bar)}"
  IO.FS.removeDirAll d
LEAN

cat > Elab.lean <<'LEAN'
import Lean
open Lean Elab Term

elab "pathProbe%" : term => do
  let d ← IO.FS.createTempDir
  let a := d / "a"
  let b := d / "b"
  IO.FS.createDirAll (b / "Foo")
  IO.FS.createDirAll a
  let sp : SearchPath := [a, b]
  discard <| sp.findWithExt "olean" `Foo.Bar
  IO.FS.createDirAll (a / "Foo")
  let r ← sp.findWithExt "olean" `Foo.Bar
  let n := if r == some (a / "Foo" / "Bar.olean") then 1 else 2
  IO.FS.removeDirAll d
  return mkNatLit n

def chosen : Nat := pathProbe%
example : chosen = 1 := rfl
LEAN

cat > lookup.expected <<'EOF_EXPECTED'
before: /b/Foo/Bar.olean
after: /a/Foo/Bar.olean
removed: /b/Foo/Bar.olean
file: /a/Foo/Bar.olean
EOF_EXPECTED

for exact in "" 1; do
  env ${exact:+PAPERLEAN_EXACT=1} lean Lookup.lean > lookup.out 2>&1 ||
    fail "the lookups failed (exact=$exact): $(cat lookup.out)"
  $DIFF lookup.expected lookup.out || fail "the lookups differ from official Lean's (exact=$exact)"
  env ${exact:+PAPERLEAN_EXACT=1} lean -DmaxHeartbeats=0 -DmaxRecDepth=0 Elab.lean > elab.out 2>&1 ||
    fail "the elaborator's result differs from official Lean's (exact=$exact): $(cat elab.out)"
done
