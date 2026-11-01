# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that section variables whose elaboration uses state outside the environment are not reused
# when it may have changed: environment variables through libuv, the working directory, changes of the
# file system and of access rights, the standard streams, a stream of a file opened at initialization,
# the state of a promise, a reference kept in an extension's state or in a global reference, a global
# reference that the elaboration changes, and a global reference that changed since (the random
# generator's). All of these are elaborators that are not on the whitelist (`Lean.PaperLean.Whitelist`),
# and no recording of them is used. Each file gives what Lean gives, i.e. what PaperLean gives when it
# reuses nothing (`PAPERLEAN_EXACT`), and the debug log (`PAPERLEAN_DEBUG_REUSE`) says why.

unset PAPERLEAN_EXACT PAPERLEAN_REUSE_ORACLE PAPERLEAN_REUSE_STATS
export PAPERLEAN_REUSE=1
cd "$TMP_DIR"
mkdir -p sub lib
header='import Lean.Elab.ElabRules
import Std.Internal.UV.System
open Lean Elab Term
def propOf (b : Bool) : Expr := if b then mkConst ``True else mkConst ``False'

# elaborators whose state comes from initialization or from other commands
cat > ExtsA.lean <<'EOF'
import Lean.Elab.ElabRules
open Lean Elab Term Command
def propOf (b : Bool) : Expr := if b then mkConst ``True else mkConst ``False
initialize flagExt : EnvExtension (Option (IO.Ref Bool)) ← registerEnvExtension (pure none)
elab "extflag%" : term => do
  let some r := flagExt.getState (← getEnv) | return mkConst ``True
  return propOf (← r.get)
elab "mkextflag" : command => do
  let r ← IO.mkRef true
  modifyEnv (flagExt.setState · (some r))
elab "clearextflag" : command => do
  let some r := flagExt.getState (← getEnv) | return
  r.set false
initialize innerRef : IO.Ref (Option (IO.Ref Bool)) ← IO.mkRef none
elab "innerflag%" : term => do
  let some r ← innerRef.get | return mkConst ``True
  return propOf (← r.get)
elab "mkinnerflag" : command => do innerRef.set (some (← IO.mkRef true))
elab "clearinnerflag" : command => do
  let some r ← innerRef.get | return
  r.set false
initialize counter : IO.Ref Nat ← IO.mkRef 0
elab "odd%" : term => do return propOf ((← counter.modifyGet fun n => (n, n + 1)) % 2 == 1)
initialize lines : IO.FS.Stream ← IO.FS.Stream.ofHandle <$> IO.FS.Handle.mk "lines.txt" .read
elab "nextline%" : term => do return propOf ((← lines.getLine).trimAscii.toString == "1")
initialize promRef : IO.Ref (Option (IO.Promise Unit)) ← IO.mkRef none
elab "pending%" : term => do
  let some p ← promRef.get | return mkConst ``True
  return propOf !(← IO.hasFinished p.result?)
elab "mkprom" : command => do promRef.set (some (← IO.Promise.new))
elab "resolveprom" : command => do
  let some p ← promRef.get | return
  p.resolve ()
elab "ro%" : term => do
  IO.setAccessRights "probe_file" { user := { read := true } }
  return mkConst ``True
elab "rw%" : term => do
  IO.setAccessRights "probe_file" { user := { read := true, write := true } }
  return mkConst ``True
elab "writable%" : term => do
  return propOf (← try IO.FS.withFile "probe_file" .append (fun _ => pure ()); pure true catch _ => pure false)
EOF
printf '1\n' > lines.txt
lean -o lib/ExtsA.olean ExtsA.lean > exts.out 2>&1 || fail "ExtsA.lean failed: $(cat exts.out)"

# In Lean, `t1` does not typecheck: the state changed, so `h` became `False`.
cat > UvEnv.lean <<EOF
$header
elab "flag%" : term => do return propOf ((← Std.Internal.UV.System.osGetenv "PL_FLAG") == some "1")
#eval Std.Internal.UV.System.osSetenv "PL_FLAG" "1"
variable (h : flag%)
include h
theorem t0 : True := trivial
#eval Std.Internal.UV.System.osSetenv "PL_FLAG" "0"
theorem t1 : True := h
EOF
cat > GlobalRef.lean <<EOF
$header
elab "seed1%" : term => do return propOf ((← IO.stdGenRef.get).s1 == (mkStdGen 1).s1)
#eval IO.setRandSeed 1
variable (h : seed1%)
include h
theorem t0 : True := trivial
#eval IO.setRandSeed 2
theorem t1 : True := h
EOF
cat > WorkingDir.lean <<EOF
$header
elab "insub%" : term => do return propOf ((← IO.Process.getCurrentDir).fileName == some "sub")
#eval IO.Process.setCurrentDir "sub"
variable (h : insub%)
include h
theorem t0 : True := trivial
#eval IO.Process.setCurrentDir ".."
theorem t1 : True := h
EOF
cat > ExtRef.lean <<'EOF'
import ExtsA
mkextflag
variable (h : extflag%)
include h
theorem t0 : True := trivial
clearextflag
theorem t1 : True := h
EOF
cat > InnerRef.lean <<'EOF'
import ExtsA
mkinnerflag
variable (h : innerflag%)
include h
theorem t0 : True := trivial
clearinnerflag
theorem t1 : True := h
EOF
cat > Promise.lean <<'EOF'
import ExtsA
mkprom
variable (h : pending%)
include h
theorem t0 : True := trivial
resolveprom
theorem t1 : True := h
EOF
# In Lean, each elaboration advances the counter, so the variable is `True` and `False` in turn.
cat > Counter.lean <<'EOF'
import ExtsA
variable (h : odd%)
include h
theorem t0 : True := trivial
theorem t1 : True := trivial
theorem t2 : True := h
theorem t3 : True := h
EOF
# In Lean, the elaborator reads the next line for each declaration.
cat > Handle.lean <<'EOF'
import ExtsA
variable (h : nextline%)
include h
theorem t0 : True := trivial
theorem t1 : True := h
EOF
# In Lean, `t1` makes the file read-only again, so `writable%` is `False`.
cat > Chmod.lean <<'EOF'
import ExtsA
variable (h : ro%)
include h
theorem t0 : True := trivial
omit h in theorem tm : rw% := trivial
theorem t1 : True := trivial
omit h in theorem t2 : writable% := trivial
EOF
# In Lean, the variable is `False` in `t0`, whose elaboration finds the directory that the `variable`
# command created, and `True` in `t1`.
cat > FsChange.lean <<EOF
$header
elab "created%" : term => do return propOf (← try IO.FS.createDir "probe_dir"; pure true catch _ => pure false)
variable (h : created%)
include h
theorem t0 : True := trivial
#eval IO.FS.removeDir "probe_dir"
theorem t1 : True := trivial
#check @t0
#check @t1
EOF
# In Lean, the elaborator prints for every declaration that elaborates the variables.
cat > Streams.lean <<EOF
$header
elab "probe%" : term => do IO.println "elaborated"; return mkConst \`\`Nat
variable (x : probe%)
include x
theorem t0 : True := trivial
theorem t1 : True := trivial
EOF

# the state that the files read, as at the start of each run
reset() {
  printf '1\n1\n0\n0\n0\n' > lines.txt
  touch probe_file
  chmod u+w probe_file
  if [ -d probe_dir ]; then rmdir probe_dir; fi
}
for f in UvEnv GlobalRef WorkingDir ExtRef InnerRef Promise Counter Handle Chmod FsChange Streams; do
  set +e
  reset; LEAN_PATH=lib lean $f.lean > $f.reuse.out 2>&1; r1=$?
  reset; PAPERLEAN_EXACT=1 LEAN_PATH=lib lean $f.lean > $f.exact.out 2>&1; r2=$?
  reset; PAPERLEAN_DEBUG_REUSE=1 LEAN_PATH=lib lean $f.lean > $f.debug.out 2>&1
  set -e
  [ $r1 = $r2 ] && cmp -s $f.reuse.out $f.exact.out ||
    fail "$f.lean differs from a run that reuses nothing (exit $r1 vs $r2):
$(diff $f.reuse.out $f.exact.out)"
  grep -q "section variables not kept: not recordable: .*not on the whitelist" $f.debug.out ||
    fail "$f.lean: the debug log does not say why: $(grep PaperLean $f.debug.out)"
  # (a file whose state does not change in Lean tests nothing)
  case $f in
    FsChange) grep -q "t0 : False → True" $f.exact.out && grep -q "t1 : True → True" $f.exact.out;;
    Streams) [ "$(grep -c elaborated $f.exact.out)" = 3 ];;
    *) grep -q "Type mismatch" $f.exact.out;;
  esac || fail "$f.lean does not test what it should: $(cat $f.exact.out)"
done
chmod u+w probe_file
