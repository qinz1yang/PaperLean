# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests `isNoncomputable` (`Lean.Compiler.NoncomputableAttr`), which reads the tags of a theorem of
# the module or of a declaration not declared yet without waiting for earlier proofs and kernel
# checks: its answers and the errors of `inferInstanceAs`, which asks it about the instance being
# declared, are official Lean's (the expected output below is official Lean's); and such questions
# do not wait for an earlier proof (which here waits for a later command).

cat > "$TMP_DIR/Tags.lean" <<'EOF2'
import Lean
open Lean Elab Command
elab "chk " n:ident : command => do
  logInfo m!"{n.getId}: {isNoncomputable (← getEnv) n.getId}"
structure Box where
  val : Nat
theorem thm : True := trivial
noncomputable def ncd : Nat := Classical.choice ⟨0⟩
def cd : Nat := 0
noncomputable section
def autoNc : Nat := Classical.choice ⟨0⟩
theorem thmInNc : True := trivial
end
noncomputable instance ncInst : Inhabited Box := ⟨⟨Classical.choice ⟨0⟩⟩⟩
def Box' := Box
-- `inferInstanceAs` compiles a wrapper, whose errors it logs unless the instance is noncomputable
noncomputable instance ncWrap : Inhabited Box' := inferInstanceAs (Inhabited Box)
instance cWrap : Inhabited Box' := inferInstanceAs (Inhabited Box)
chk thm
chk ncd
chk cd
chk autoNc
chk thmInNc
chk ncInst
chk ncWrap
chk cWrap
chk undeclared
chk Nat.add
chk Classical.choice
EOF2
cat > "$TMP_DIR/expected.out" <<'EOF2'
Tags.lean:18:35: error(lean.dependsOnNoncomputable): `Classical.choice` not supported by code generator; consider marking definition as `noncomputable`
Tags.lean:18:9: error(lean.dependsOnNoncomputable): failed to compile definition, consider marking it as 'noncomputable' because it depends on 'cWrap._aux_1', which is 'noncomputable'
thm: false
ncd: true
cd: false
autoNc: true
thmInNc: false
ncInst: true
ncWrap: true
cWrap: true
undeclared: false
Nat.add: false
Classical.choice: false
EOF2
cd "$TMP_DIR"
lean Tags.lean > tags.out 2>&1 && fail "Tags.lean did not fail as in Lean"
$DIFF -- expected.out tags.out || fail "the output differs from Lean's"
# a theorem whose proof waits for a later command: questions about it and about a name not declared
# yet do not wait for the proof
cat > NoWait.lean <<'EOF2'
import Lean
open Lean Elab Command
elab "chk " n:ident : command => do
  logInfo m!"{n.getId}: {isNoncomputable (← getEnv) n.getId}"
elab "go" : command => IO.FS.writeFile "go" ""
theorem slow : True := by
  run_tac do
    let mut n := 0
    while !(← System.FilePath.pathExists "go") && n < 200 do
      IO.sleep 50
      n := n + 1
    unless ← System.FilePath.pathExists "go" do
      throwError "the main thread waited for this proof"
  trivial
chk slow
chk notYet
go
EOF2
rm -f go
lean NoWait.lean > no_wait.out 2>&1 || fail "a question waited for an earlier proof: $(cat no_wait.out)"
printf 'slow: false\nnotYet: false\n' | $DIFF -- - no_wait.out || fail "NoWait.lean: unexpected output"
