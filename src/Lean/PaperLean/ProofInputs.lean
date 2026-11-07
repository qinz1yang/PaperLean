/-
Copyright (c) 2026 PaperLean contributors. Released under Apache 2.0.
-/
module
prelude
public import Lean.Environment
import Lean.PaperLean.Base

namespace Lean.PaperLean.ProofInputs

register_builtin_option paperlean.proofConversion : Bool := {
  defValue := true
  descr := "construct checked congruence proofs for conversions under repeated reducible applications"
}

public def enabled (opts : Options) : Bool := paperlean.proofConversion.get opts

-- Eager definitions passed to the ordinary declaration builder, local to this environment
-- branch. Custom/pending constant tasks cannot enter this table and are never forced.
private builtin_initialize defs : EnvExtension (Nat × PHashMap Name (DefinitionVal × Bool)) ←
  registerEnvExtension (pure (0, {})) (asyncMode := .local)

public def record (env : Environment) (decl : Declaration) (opts : Options) (exported : Bool) : BaseIO Environment := do
  let .defnDecl d := decl | return env
  if !paperlean.proofConversion.get opts || !PaperLean.nativeAvailable d || d.safety != .safe then
    return env
  let start ← IO.getNumHeartbeats
  try
    if d.all != [d.name] then return env
    let (count,m) := defs.getState (asyncMode := .local) env
    if count >= 256 then return env
    return defs.setState (asyncMode := .local) env (count+1, m.insert d.name (d,exported))
  finally
    PaperLean.setHeartbeats start

public def lookup (env : Environment) (n : Name) (privateKernel := false) : Option DefinitionVal := do
  let (d,exported) ← (defs.getState (asyncMode := .local) env).2.find? n
  guard (privateKernel || !env.isExporting || exported)
  return d

end Lean.PaperLean.ProofInputs
