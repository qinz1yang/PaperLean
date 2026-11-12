# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# The quoted-syntax fast path for auto-param tactics (`Lean.PaperLean.QuotedSyntax.ofConstant?`)
# must reject a `noncomputable` definition like evaluation does, also when the tag is on the branch
# that elaborated the definition (a `mutual` block, elaborated apart from the command's branch)
# rather than on the branch that uses it. The fast path and evaluation (`PAPERLEAN_QUOTED_SYNTAX=0`)
# must give the same messages, in a file of the module system and in one without.

cd "$TMP_DIR"
for header in "" "module"; do
  cat > Mut.lean <<EOF
$header
import Lean
open Lean

mutual
  noncomputable def ncTac : Syntax :=
    Syntax.node SourceInfo.none
      (Name.mkStr4 "Lean" "Parser" "Tactic" "tacticTrivial")
      (Array.empty : Array Syntax)
  noncomputable def other : Nat := 0
end

theorem withTac (h : autoParam True ncTac) : True := h
example : True := withTac
EOF
  for v in "" 0; do
    capture_only "" env PAPERLEAN_QUOTED_SYNTAX="$v" lean Mut.lean
    { cat "$CAPTURED.out.produced"; echo "exit $EXIT"; } > "$TMP_DIR/Mut.${header:-plain}.${v:-fast}.out"
  done
  grep -q 'exit 0' "$TMP_DIR/Mut.${header:-plain}.0.out" && fail "${header:-plain} file: evaluation accepted the tactic"
  $DIFF -- "$TMP_DIR/Mut.${header:-plain}.0.out" "$TMP_DIR/Mut.${header:-plain}.fast.out" ||
    fail "${header:-plain} file: the fast path accepts a noncomputable tactic that evaluation rejects"
done
true
