# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# `runFrontend` computes the contents of the `.ilean` file while it writes the `.olean` file. The
# `.ilean` file is still written after the `.olean` file, with the same contents, and not at all if
# writing the `.olean` file fails.

cd "$TMP_DIR"
cat > M.lean <<'EOF2'
def foo := 1
theorem bar : foo = 1 := rfl
example : bar = bar := rfl
EOF2
run lean M.lean -o M.olean -i M.ilean
[ -s M.olean ] || fail "no .olean file"
grep -q '"module":"M"' M.ilean || fail "the .ilean file does not name the module"
grep -qF '\"n\":\"foo\"' M.ilean || fail "the .ilean file has no reference to foo"
grep -qF '\"n\":\"bar\"' M.ilean || fail "the .ilean file has no reference to bar"
# the same contents without the `.olean` file
run lean M.lean -i M2.ilean
cmp M.ilean M2.ilean || fail "the .ilean file depends on whether an .olean file is written"
# an `.olean` file that cannot be written (its directory is a regular file): no `.ilean` file
touch notadir
capture_fail lean M.lean -o notadir/M.olean -i M3.ilean
[ ! -e M3.ilean ] || fail "the .ilean file was written although the .olean file could not be"
