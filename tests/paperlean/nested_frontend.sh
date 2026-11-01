# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests frontend runs inside a frontend run: one inside `#eval` that succeeds, reports an error or
# throws, under an outer file that succeeds or fails, and frontend runs nested twice, each with
# official Lean's output and exit code (the expected outputs below are official Lean 4.35.0-rc3's),
# without reuse, with `PAPERLEAN_EXACT=1`, and asked to reuse with the oracle, where the second
# frontend of the process turns both off with a message on the standard error.

cd "$TMP_DIR"

cat > Success.lean <<'EOF'
import Lean
/-! A frontend run inside `#eval`, while the outer one reports. -/
#eval show IO Unit from do
  IO.println "before nested frontend"
  unsafe Lean.enableInitializersExecution
  discard <| Lean.Elab.runFrontend "#eval 123\n" {} "Inner.lean" `Inner
  IO.println "after nested frontend"
#eval 456
EOF
cat > Success.expected <<'EOF'
before nested frontend
123
after nested frontend
456
EOF

cat > InnerError.lean <<'EOF'
import Lean
/-! A nested frontend that reports an error: the outer one goes on and succeeds. -/
#eval show IO Unit from do
  IO.println "before nested frontend"
  unsafe Lean.enableInitializersExecution
  let r ← Lean.Elab.runFrontend "#check innerNonexistent\n#eval 123\n" {} "Inner.lean" `Inner
  IO.println s!"after nested frontend: {r.isSome}"
#eval 456
EOF
cat > InnerError.expected <<'EOF'
before nested frontend
Inner.lean:1:7: error(lean.unknownIdentifier): Unknown identifier `innerNonexistent`
123
after nested frontend: false
456
EOF

cat > OuterError.lean <<'EOF'
import Lean
/-! An error of the outer frontend after a nested one: its diagnostic must be reported. -/
#eval show IO Unit from do
  IO.println "before nested frontend"
  unsafe Lean.enableInitializersExecution
  discard <| Lean.Elab.runFrontend "#eval 123\n" {} "Inner.lean" `Inner
  IO.println "after nested frontend"
#eval 456

#check outerNonexistent
EOF
cat > OuterError.expected <<'EOF'
before nested frontend
123
after nested frontend
456
OuterError.lean:10:7: error(lean.unknownIdentifier): Unknown identifier `outerNonexistent`
EOF

cat > Thrown.lean <<'EOF'
import Lean
/-! A nested frontend that throws: the outer one goes on. -/
#eval show IO Unit from do
  IO.println "before nested frontend"
  unsafe Lean.enableInitializersExecution
  try
    discard <| Lean.Elab.runFrontend "#eval 123\n" {} "Inner.lean" `Inner
      (incrLoadFileName? := some "does-not-exist.snapshot")
  catch _ => IO.println "the nested frontend failed"
  IO.println "after nested frontend"
#eval 456
EOF
cat > Thrown.expected <<'EOF'
before nested frontend
the nested frontend failed
after nested frontend
456
EOF

cat > Deep.lean <<'EOF'
import Lean
/-! A frontend inside a frontend inside a frontend. -/
def middle : String := "import Lean
#eval show IO Unit from do
  IO.println \"middle before\"
  unsafe Lean.enableInitializersExecution
  discard <| Lean.Elab.runFrontend \"#eval 123\\n\" {} \"Innermost.lean\" `Innermost
  IO.println \"middle after\"
#eval 789
"
#eval show IO Unit from do
  IO.println "outer before"
  unsafe Lean.enableInitializersExecution
  discard <| Lean.Elab.runFrontend middle {} "Middle.lean" `Middle
  IO.println "outer after"
#eval 456
EOF
cat > Deep.expected <<'EOF'
outer before
middle before
123
middle after
789
outer after
456
EOF

# <file> <expected exit code>: its output and exit code without reuse, with the oracle and exact
check() {
  local f=$1 code=$2 mode r
  for mode in "" PAPERLEAN_EXACT=1 "PAPERLEAN_REUSE=1 PAPERLEAN_REUSE_ORACLE=1"; do
    r=0
    env $mode lean $f.lean > $f.out 2> $f.err || r=$?
    [ "$r" = "$code" ] || fail "$f.lean exits with $r, not $code ($mode): $(cat $f.out $f.err)"
    $DIFF -- $f.expected $f.out || fail "the output of $f.lean differs from Lean's ($mode)"
  done
  # (`Thrown` ends before its frontend starts)
  [ $f = Thrown ] || grep -q "PaperLean: a further frontend in this process (.*): reuse of results and its oracle are off" $f.err ||
    fail "$f.lean did not say that reuse is off: $(cat $f.err)"
}
check Success 0
check InnerError 0
check OuterError 1
check Thrown 0
check Deep 0
