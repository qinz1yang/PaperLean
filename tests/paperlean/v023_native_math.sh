# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
case "$(uname -s)" in Darwin|Linux) ;; *) exit 0 ;; esac
cd "$TMP_DIR"
mkdir -p dep/D root
cat > dep/lakefile.toml <<'END'
name = "mathdeps"
defaultTargets = ["D"]
[[lean_lib]]
name = "D"
globs = ["D", "D.+"]
END
cat > root/lakefile.toml <<'END'
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "mathdeps"
path = "../dep"
[[lean_lib]]
name = "Root"
END
cat > dep/D/Good.lean <<'END'
@[noinline] def mathValue (x y : Float) : Float :=
  Float.pow x y + Float.sqrt x + Float.ceil x + Float.floor x
END
cat > dep/D/Foreign.lean <<'END'
@[extern "pow"] def foreignValue (x y : Nat) : Nat := x + y + 41
END
cat > dep/D/CallsForeign.lean <<'END'
import D.Foreign
@[noinline] def callsForeign (x y : Nat) : Nat := foreignValue x y
END
cat > dep/D/Same.lean <<'END'
@[extern "pow"] def foreignFloat (x y : Float) : Float := x + y + 41
END
cat > dep/D/CallsSame.lean <<'END'
import D.Same
@[noinline] def callsSame (x y : Float) : Float := foreignFloat x y
END
cat > dep/D/Override.lean <<'END'
@[export pow] def overridePow (x y : Float) : Float := x + y + 41
END
cat > dep/D.lean <<'END'
import D.Good
import D.CallsForeign
import D.CallsSame
import D.Override
END
echo 'import D' > root/Root.lean
cat > root/Good.lean <<'END'
import D.Good
#eval (mathValue 4 2).toUInt64
END
cat > root/Bad.lean <<'END'
import D.CallsForeign
#eval callsForeign 3 4
END
cat > root/Same.lean <<'END'
import D.CallsSame
#eval (callsSame 3 4).toUInt64
END
cd root
run lake build
capture lake paperlean prepare -j 2
check_out_contains "Prepared"
capture lake paperlean status --verify
check_out_contains "D.Override runs in the interpreter"
check_out_contains "D.Foreign runs in the interpreter"
check_out_contains "D.Same runs in the interpreter"
check_out_contains "D.CallsSame runs in the interpreter"
capture lake lean Good.lean
cp "$CAPTURED.out.produced" "$TMP_DIR/Good.plain"
capture env PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean Good.lean
check_out_contains "native libs=1 modules=1 "
check_out_contains "26"
{ grep -v '^paperlean-' "$CAPTURED.out.produced" || true; } | $DIFF -- "$TMP_DIR/Good.plain" - ||
  fail "native math changed Good"
# The interpreter refuses this user extern. The spelling cannot authorize native code.
capture_exit 1 lake lean Bad.lean
check_out_contains "Could not find native implementation of external declaration 'foreignValue'"
cp "$CAPTURED.out.produced" "$TMP_DIR/Bad.plain"
capture_exit 1 env PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean Bad.lean
check_out_contains "Could not find native implementation of external declaration 'foreignValue'"
{ grep -v '^paperlean-' "$CAPTURED.out.produced" || true; } | $DIFF -- "$TMP_DIR/Bad.plain" - ||
  fail "native math accepted a user extern with an incompatible signature"
# Even a user-declared ABI that matches the real Float primitive must keep its interpreter policy.
capture_exit 1 lake lean Same.lean
check_out_contains "Could not find native implementation of external declaration 'foreignFloat'"
cp "$CAPTURED.out.produced" "$TMP_DIR/Same.plain"
capture_exit 1 env PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean Same.lean
check_out_contains "Could not find native implementation of external declaration 'foreignFloat'"
{ grep -v '^paperlean-' "$CAPTURED.out.produced" || true; } | $DIFF -- "$TMP_DIR/Same.plain" - ||
  fail "an imported user extern silently became the standard math operation"
