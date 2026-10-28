/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Util.ReplaceExpr
import Lean.PaperLean.Base

public section

namespace Lean.Expr

/--
Instantiate level parameters
-/
@[specialize] def instantiateLevelParamsCore (s : Name → Option Level) (e : Expr) : Expr :=
  e.replace replaceFn
where
  @[specialize] replaceFn (e : Expr) : Option Expr :=
    if !e.hasLevelParam then e else match e with
    | const _ us => e.updateConst! (us.map fun u => u.substParams s)
    | sort u => e.updateSort! (u.substParams s)
    | _ => none

private def getParamSubst : List Name → List Level → Name → Option Level
  | p::ps, u::us, p' => if p == p' then some u else getParamSubst ps us p'
  | _,     _,     _  => none

/-- The `const` and `sort` case of `instantiateLevelParamsCore.replaceFn`, for
`instantiateLevelParamsNative`. -/
@[export lean_paperlean_inst_lparams_leaf]
private def instantiateLevelParamsLeaf (e : Expr) (paramNames : List Name) (lvls : List Level) : Expr :=
  (instantiateLevelParamsCore.replaceFn (getParamSubst paramNames lvls) e).getD e

/-- `instantiateLevelParamsCore (getParamSubst paramNames lvls) e`, computed by the same traversal
in native code, which calls back `instantiateLevelParamsLeaf` only for `const` and `sort` nodes with
level parameters. -/
@[extern "lean_paperlean_instantiate_level_params"]
private opaque instantiateLevelParamsNative (e : @& Expr) (paramNames : List Name)
    (lvls : List Level) : Expr

/--
Instantiate universe level parameters names `paramNames` with `lvls` in `e`.
If the two lists have different length, the smallest one is used.
-/
-- PaperLean: (not inlined, so that compiled callers in other packages call it as upstream's)
@[noinline] def instantiateLevelParams (e : Expr) (paramNames : List Name) (lvls : List Level) : Expr :=
  if paramNames.isEmpty || lvls.isEmpty then e else
  -- PaperLean: in native code (`src/paperlean/inst_lparams.cpp`)
  if PaperLean.nativeAvailable e then instantiateLevelParamsNative e paramNames lvls else
    instantiateLevelParamsCore (getParamSubst paramNames lvls) e

/--
Instantiate universe level parameters names `paramNames` with `lvls` in `e`.
If the two lists have different length, the smallest one is used.
(Does not preserve expression sharing.)
-/
def instantiateLevelParamsNoCache (e : Expr) (paramNames : List Name) (lvls : List Level) : Expr :=
  if paramNames.isEmpty || lvls.isEmpty then e else
    e.replaceNoCache (instantiateLevelParamsCore.replaceFn (getParamSubst paramNames lvls))

private partial def getParamSubstArray (ps : Array Name) (us : Array Level) (p' : Name) (i : Nat) : Option Level :=
  if h : i < ps.size then
    let p := ps[i]
    if h : i < us.size then
      let u := us[i]
      if p == p' then some u else getParamSubstArray ps us p' (i+1)
    else none
  else none

/--
Instantiate universe level parameters names `paramNames` with `lvls` in `e`.
If the two arrays have different length, the smallest one is used.
-/
def instantiateLevelParamsArray (e : Expr) (paramNames : Array Name) (lvls : Array Level) : Expr :=
  if paramNames.isEmpty || lvls.isEmpty then e else
    e.instantiateLevelParamsCore fun p =>
      getParamSubstArray paramNames lvls p 0
-- Modified by PaperLean.
