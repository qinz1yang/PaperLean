# The options in effect at the definition determine the type of the exported equation.
# Compile fresh producers; no generated equation can be inherited from another run.
official="${OFFICIAL_LEAN_TOOLCHAIN:-$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3}/bin/lean"
[ -x "$official" ] || fail "official Lean rc3 not found: $official"
src="$TEST_DIR/paperlean/equation_options"
for jobs in 1 4; do
  for force in true false; do
    dir="$TMP_DIR/j$jobs-$force"
    mkdir -p "$dir"
    cp "$src"/{Equations,Use}.lean "$dir"
    cd "$dir"
    export LEAN_PATH="$dir"
    run lean "-j$jobs" "-Dbackward.isDefEq.respectTransparency.types=$force" -o Equations.olean Equations.lean
    if [ "$force" = true ]; then reader=false; else reader=true; fi
    run lean "-j$jobs" "-Dbackward.isDefEq.respectTransparency.types=$reader" -o Use.olean Use.lean
    if [ "$jobs/$force" = 1/true ]; then
      run env -u LEAN_SYSROOT "$official" -j1 "-Dbackward.isDefEq.respectTransparency.types=$reader" Use.lean
    fi
  done
done

# rc3 does not save the new option keys. A previously generated rc3 equation retains
# its exact signature when consumed by the candidate under different options.
dir="$TMP_DIR/rc3"
mkdir -p "$dir"
cp "$src"/{Equations,Use}.lean "$dir"
cd "$dir"
export LEAN_PATH="$dir"
run env -u LEAN_SYSROOT "$official" -j1 -Dbackward.isDefEq.respectTransparency.types=false -o Equations.olean Equations.lean
run lean -j4 -Dbackward.isDefEq.respectTransparency.types=true -o Use.olean Use.lean

# Both branches publicly use a fresh producer's equation under opposite reader options.
check_diamond () {
  caseName=$1; arity=$2; parent=$3; types=$4; shift 4
  dir="$TMP_DIR/diamond-$caseName"
  mkdir -p "$dir"
  cp "$src"/{Equations,DeferredUse}.lean "$dir"
  if [ "$caseName" = structuralDefault ]; then
    cp "$src/Deferred.lean" "$dir"
  else
    cp "$src/DeferredWF.lean" "$dir/Deferred.lean"
  fi
  cd "$dir"
  export LEAN_PATH="$dir"
  run lean -j1 -o Equations.olean Equations.lean
  run lean -j1 "$@" -o Deferred.olean Deferred.lean
  for branch in Left Right; do
    cat >"$branch.lean" <<EOF
module
public import Deferred
set_option linter.defProp false in
@[expose] public def equation$branch := @Walk.deferred.eq_2
EOF
    if [ "$branch" = Left ]; then
      run lean -j4 -Dbackward.isDefEq.respectTransparency.types=false -o Left.olean Left.lean
    elif [ "$caseName" = structuralDefault ]; then
      # PaperLean can prove the strict structural unfold lemma. Stock consumes
      # both independently realized results in the merge below.
      run lean -j1 -Dbackward.isDefEq.respectTransparency.types=true -o Right.olean Right.lean
    else
      run env -u LEAN_SYSROOT "$official" -j1 -Dbackward.isDefEq.respectTransparency.types=true -o Right.olean Right.lean
    fi
  done
  for first in Left Right; do
    if [ "$first" = Left ]; then second=Right; else second=Left; fi
    cat >Merge.lean <<EOF
module
public import $first
public import $second
import Lean
open Lean
run_meta do
  for name in [\`\`Walk.deferred.eq_2, \`\`equationLeft, \`\`equationRight] do
    let type := (← getConstInfo name).type
    unless type.getForallArity == $arity do
      throwError "unexpected signature for {name}: {type}"
  let settings := (Lean.Meta.eqnOptionsExt.find? (← getEnv) \`\`Walk.deferred).getD #[]
  unless settings.contains (\`backward.isDefEq.respectTransparency, DataValue.ofBool $parent) &&
      settings.contains (\`backward.isDefEq.respectTransparency.types, DataValue.ofBool $types) do
    throwError "missing producer transparency settings"
EOF
    run lean -j4 Merge.lean
    run env -u LEAN_SYSROOT "$official" -j1 Merge.lean
  done
  if [ "$arity" = 6 ]; then
    run lean -j4 -Dbackward.isDefEq.respectTransparency.types=true DeferredUse.lean
  fi
}

check_diamond default 5 true true
check_diamond typesPermissive 6 true false -Dbackward.isDefEq.respectTransparency.types=false
check_diamond parentPermissive 6 false true -Dbackward.isDefEq.respectTransparency=false
check_diamond parentOverridesTypes 6 false true -Dbackward.isDefEq.respectTransparency=false -Dbackward.isDefEq.respectTransparency.types=true
check_diamond bothPermissive 6 false false -Dbackward.isDefEq.respectTransparency=false -Dbackward.isDefEq.respectTransparency.types=false
check_diamond structuralDefault 5 true true

# The permissive producer setting retains the structural equation with an extra premise.
# Select it on the original definition and require both readers to accept that application.
dir="$TMP_DIR/structural"
mkdir -p "$dir"
cp "$src"/{Equations,Deferred,DeferredUse}.lean "$dir"
cd "$dir"
export LEAN_PATH="$dir"
run lean -j1 -o Equations.olean Equations.lean
run lean -j1 -Dbackward.isDefEq.respectTransparency.types=false -o Deferred.olean Deferred.lean
for reader in true false; do
  run lean -j4 "-Dbackward.isDefEq.respectTransparency.types=$reader" DeferredUse.lean
  run env -u LEAN_SYSROOT "$official" -j1 "-Dbackward.isDefEq.respectTransparency.types=$reader" DeferredUse.lean
done

# A unary well-founded function can acquire its first realization context before
# the general mutual-definition path. Check that snapshot directly.
dir="$TMP_DIR/local-wf"
mkdir -p "$dir"
cp "$src/LocalWF.lean" "$dir"
cd "$dir"
export LEAN_PATH="$dir"
for jobs in 1 4; do
  run lean "-j$jobs" -Dbackward.isDefEq.respectTransparency.types=true LocalWF.lean
done

# Known constructors give a rewrite-ready equation in the producing module. A matcher
# first requested downstream must give official and candidate consumers identical types.
dir="$TMP_DIR/finish"
mkdir -p "$dir"
cp "$src"/{Finish,FinishUse}.lean "$dir"
cd "$dir"
export LEAN_PATH="$dir"
run lean -j4 -o Finish.olean Finish.lean
run lean -j4 FinishUse.lean
run env -u LEAN_SYSROOT "$official" -j1 FinishUse.lean
for branch in Left Right; do
  cat >"$branch.lean" <<EOF
module
public import Finish
set_option linter.defProp false in
@[expose] public def eq$branch := @V.delayed.eq_2
EOF
done
run lean -j4 -Dbackward.isDefEq.respectTransparency.types=false -o Left.olean Left.lean
run env -u LEAN_SYSROOT "$official" -j1 -Dbackward.isDefEq.respectTransparency.types=true -o Right.olean Right.lean
for first in Left Right; do
  if [ "$first" = Left ]; then second=Right; else second=Left; fi
  printf 'module\npublic import %s\npublic import %s\n' "$first" "$second" >Merge.lean
  run lean -j4 Merge.lean
  run env -u LEAN_SYSROOT "$official" -j1 Merge.lean
done

# Unannotated nonrecursive eliminators publish branch equations usable by rw.
# Verify locally reused matcher information at each job setting and check genuinely
# deferred mixed-compiler branches in both import orders.
check_eliminators () {
  local caseName=$1; shift
  local dir="$TMP_DIR/eliminators-$caseName"
  mkdir -p "$dir"
  cp "$src"/{Finish,Eliminate,EliminateUse,EliminatePolicy}.lean "$dir"
  cd "$dir"
  export LEAN_PATH="$dir"
  run lean -j1 -o Finish.olean Finish.lean
  run lean "$@" -o Eliminate.olean Eliminate.lean
  local expected=false
  if [[ "$caseName" = strict* ]]; then expected=true; fi
  run env -u LEAN_SYSROOT PAPERLEAN_TEST_EQUATION_TYPES="$expected" "$official" -j1 EliminatePolicy.lean
  for branch in Left Right; do
    cat >"$branch.lean" <<EOF
module
public import Eliminate
set_option linter.defProp false
@[expose] public def e${branch}1 := @V.choose.eq_1
@[expose] public def e${branch}2 := @V.choose.eq_2
@[expose] public def a${branch}1 := @V.chooseAgain.eq_1
@[expose] public def a${branch}2 := @V.chooseAgain.eq_2
@[expose] public def r${branch}1 := @V.chooseRel.eq_1
@[expose] public def r${branch}2 := @V.chooseRel.eq_2
EOF
  done
  run lean -j4 -Dbackward.isDefEq.respectTransparency.types=false -o Left.olean Left.lean
  run env -u LEAN_SYSROOT "$official" -j1 -Dbackward.isDefEq.respectTransparency.types=true -o Right.olean Right.lean
  for first in Left Right; do
    if [ "$first" = Left ]; then second=Right; else second=Left; fi
    printf 'module\npublic import %s\npublic import %s\n' "$first" "$second" >Merge.lean
    if [[ "$caseName" = strict* ]]; then
      cat >>Merge.lean <<'EOF'
import Lean
open Lean Meta
run_meta do
  for n in [``eLeft1, ``eLeft2, ``rRight1, ``rRight2] do
    let some (_, _, rhs) := (← getConstInfo n).type.getForallBody.eq? | throwError "expected equation"
    unless (isMatcherAppCore? (← getEnv) rhs).isSome do
      throwError "the explicitly strict producer policy was lost for {n}"
EOF
    else
      sed -n '/^import Lean/,$p' "$src/EliminateUse.lean" >>Merge.lean
    fi
    run lean -j4 Merge.lean
    run env -u LEAN_SYSROOT "$official" -j1 Merge.lean
  done
}
check_eliminators serial -j1
check_eliminators parallel -j4
check_eliminators default
check_eliminators strict -j1 -Dbackward.isDefEq.respectTransparency.types=true
check_eliminators strictParent -j1 -Dbackward.isDefEq.respectTransparency=true

# Official producers omit the transparency keys. Give both compilers the same
# reader settings and require their independent realizations to compose in both orders.
dir="$TMP_DIR/legacy"
mkdir -p "$dir"
cp "$src"/{Equations,Finish,Eliminate,LegacyWF,LegacyScope}.lean "$dir"
cd "$dir"
export LEAN_PATH="$dir"
for mod in Equations Finish Eliminate LegacyWF; do
  run env -u LEAN_SYSROOT "$official" -j1 -o "$mod.olean" "$mod.lean"
done
run lean -j4 -Dbackward.isDefEq.respectTransparency.types=true LegacyScope.lean
run env -u LEAN_SYSROOT "$official" -j1 -Dbackward.isDefEq.respectTransparency.types=true LegacyScope.lean
for mode in default permissive; do
  legacyFlags=()
  arity=5
  if [ "$mode" = permissive ]; then
    legacyFlags=(-Dbackward.isDefEq.respectTransparency.types=false)
    arity=6
  fi
  for stockBranch in Left Right; do
    sub="$dir/$mode-$stockBranch"
    mkdir -p "$sub"; cd "$sub"
    export LEAN_PATH="$sub:$dir"
    for branch in Left Right; do
      cat >"$branch.lean" <<EOF
module
public import Eliminate
public import LegacyWF
set_option linter.defProp false
@[expose] public def wf$branch := @Walk.legacyWF.eq_2
@[expose] public def dispatch$branch := @V.choose.eq_2
EOF
      if [ "$branch" = "$stockBranch" ]; then
        run env -u LEAN_SYSROOT "$official" -j1 "${legacyFlags[@]}" -o "$branch.olean" "$branch.lean"
      else
        run lean -j4 "${legacyFlags[@]}" -o "$branch.olean" "$branch.lean"
      fi
    done
    for first in Left Right; do
      if [ "$first" = Left ]; then second=Right; else second=Left; fi
      cat >Merge.lean <<EOF
module
public import $first
public import $second
import Lean
open Lean Meta
run_meta do
  for n in [\`\`wfLeft, \`\`wfRight] do
    unless (← getConstInfo n).type.getForallArity == $arity do
      throwError "wrong legacy WF type for {n}"
  for n in [\`\`dispatchLeft, \`\`dispatchRight] do
    let some (_, _, rhs) := (← getConstInfo n).type.getForallBody.eq? | throwError "expected equation"
    unless (isMatcherAppCore? (← getEnv) rhs).isSome == ("$mode" == "default") do
      throwError "wrong legacy dispatcher type for {n}"
EOF
      run lean -j4 Merge.lean
      run env -u LEAN_SYSROOT "$official" -j1 Merge.lean
    done
  done
done

# With opposite settings, even two stock branches from an unrecorded producer
# can publish incompatible types. The stock importer rejects that graph.
clashDir="$dir/stock-clash"
mkdir -p "$clashDir"
cp "$dir/default-Left"/Left.* "$dir/permissive-Right"/Right.* "$clashDir"
cd "$clashDir"
export LEAN_PATH="$clashDir:$dir"
printf 'module\npublic import Left\npublic import Right\n' >Clash.lean
if env -u LEAN_SYSROOT "$official" -j1 Clash.lean >clash.log 2>&1; then
  fail "stock accepted the incompatible legacy equations"
fi
run grep -F "environment already contains" clash.log

# A new private dependency of Eqns can change where downstream option references
# point. Compare the complete index against rc3 at the same source path.
dir="$TMP_DIR/navigation"
mkdir -p "$dir"
cp "$src/OptionReferences.lean" "$dir"
cd "$dir"
export LEAN_PATH="$dir"
run env -u LEAN_SYSROOT "$official" -i official.ilean OptionReferences.lean
run lean -i candidate.ilean OptionReferences.lean
run cmp official.ilean candidate.ilean
