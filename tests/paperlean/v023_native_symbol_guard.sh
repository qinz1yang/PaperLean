# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
cp v023_native_symbol_guard.lean "$TMP_DIR/Guard.lean"
cd "$TMP_DIR"
cat > Example.lean <<'END'
@[export paperlean_fixture_own] def f (n : Nat) := n + 1
END
run lean Example.lean -o Example.olean -c Example.c
cat > MathFixture.lean <<'END'
@[noinline] def mathFixture (x y : Float) : Float :=
  Float.pow x y + Float.sqrt x + Float.ceil x + Float.floor x
@[noinline] def mathFixture32 (x : Float32) : Float32 := Float32.floor x
END
run lean MathFixture.lean -o MathFixture.olean -c MathFixture.c
run lean Guard.lean -c Guard.c
run leanc -o guard Guard.c
run ./guard
run leanc -include safe.h -c Example.c -o own.o
capture_exit 1 leanc -Dpaperlean_fixture_own=other_symbol -include safe.h -c Example.c -o injected.o
check_out_contains "external name is a macro"
capture_exit 1 leanc -include macro.h -c macro.c -o macro.o
check_out_contains "external name is a macro"

case "$(uname -s)" in Darwin|Linux) ;; *) exit 0 ;; esac
# A unity compilation can force the same typed binding more than once.
run leanc -include math.h -include math.h -c MathFixture.c -o math.o
run nm -u math.o > "$TMP_DIR/math-undefined.txt"
for sym in pow sqrt ceil floor floorf; do
  grep -Eq "(^|[[:space:]])_?lean_paperlean_stdmath_${sym}$" "$TMP_DIR/math-undefined.txt" ||
    fail "missing toolchain-owned import for $sym"
  ! grep -Eq "(^|[[:space:]])_?${sym}$" "$TMP_DIR/math-undefined.txt" ||
    fail "native math binds an unowned $sym"
done
capture_exit 1 leanc -Dpow=foreign_pow -include math.h -c MathFixture.c -o injected.o
check_out_contains "external name is a macro"

# A plugin may export the same public spelling. Load it globally after Lean starts (as a
# package plugin would), call its address as a positive control, and then call generated code.
cat > competing.c <<'END'
double pow(double x, double y) { return x + y + 41; }
END
cat > check.c <<'END'
#include <dlfcn.h>
extern double l_mathFixture(double, double);
extern float l_mathFixture32(float);
int main(int argc, char **argv) {
    void *handle = dlopen(argv[1], RTLD_NOW | RTLD_GLOBAL);
    if (!handle) return 1;
    double (*shadow)(double, double) = (double (*)(double, double))dlsym(handle, "pow");
    if (!shadow || shadow(4, 2) != 47) return 2;
    if (l_mathFixture(4, 2) != 26 || l_mathFixture32(2.75f) != 2) return 3;
    return 0;
}
END
run cc -fPIC -fvisibility=default -shared competing.c -o competing.so
run cc -c check.c -o check.o
if [ "$(uname -s)" = Linux ]; then
  run leanc check.o math.o -ldl -o check
else
  run leanc check.o math.o -o check
fi
run ./check ./competing.so
