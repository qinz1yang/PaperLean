# Tests the makefile that the toolchain installs for packages (`share/lean/lean.mk`): it names no
# file of the build directory, such as the shim that only the build of Lean's own library loads
# (`paperlean/stage0_shim.c`) or an archiver that the toolchain ships in its `bin`, and `leanmake`
# builds a package's modules and static library with it.

PREFIX="$(lean --print-prefix)"
MK="$PREFIX/share/lean/lean.mk"
[ -f "$MK" ] || fail "no $MK"
BUILD_ROOT="$(dirname "$PREFIX")"
if grep -nF "$BUILD_ROOT/" "$MK"; then
  fail "$MK names files of the build directory $BUILD_ROOT"
fi
if grep -n -e "--load-dynlib" "$MK"; then
  fail "$MK loads a shared library"
fi

mkdir -p "$TMP_DIR/pkg/Foo"
cd "$TMP_DIR/pkg"
cat > Foo/A.lean <<'END'
def Foo.a : Nat := 41
END
cat > Foo.lean <<'END'
import Foo.A
def Foo.b : Nat := Foo.a + 1
END
leanmake PKG=Foo
[ -f build/Foo.olean ] && [ -f build/Foo/A.olean ] || fail "leanmake built no .olean files"
leanmake PKG=Foo lib
[ -f build/lib/libFoo.a ] || fail "leanmake built no static library"
