cd "$TMP_DIR"
cat > Example.lean <<'END'
def answer : Nat := 42
END
if [[ "$(lean --features)" == *LLVM* ]]; then
  run lean -b Example.bc Example.lean
  [ -s Example.bc ] || fail "expected LLVM bitcode"
else
  capture_exit 1 lean -o Example.olean -c Example.c -b Example.bc Example.lean
  check_out_contains "LLVM bitcode output requires a compiler built with LLVM support"
  for artifact in Example.olean Example.c Example.bc; do
    [ ! -e "$artifact" ] || fail "unexpected partial artifact: $artifact"
  done
  run lean -o Example.olean -c Example.c Example.lean
  [ -s Example.olean ] && [ -s Example.c ] || fail "expected ordinary Lean and C artifacts"
fi
