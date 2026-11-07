import Lean

open Lean Meta

run_meta do
  let transientCalls ← IO.mkRef 0
  let persistentCalls ← IO.mkRef 0
  Sym.SymM.run do
    let e ← Sym.share (mkNatLit 0)
    let p ← Sym.share (mkNatLit 1)
    let pre : Sym.Simp.Simproc := fun t => do
      if t == e then
        transientCalls.modify (· + 1)
        return .rfl (done := true) (contextDependent := true)
      persistentCalls.modify (· + 1)
      return .rfl (done := true)
    Sym.Simp.SimpM.run' (methods := { pre }) do
      let _ ← Sym.Simp.simp e
      let _ ← Sym.Simp.simp p
      withLocalDeclD `h (mkConst ``True) fun _ =>
        Sym.Simp.withFreshTransientCache do
          let _ ← Sym.Simp.simp e
          let _ ← Sym.Simp.simp p
          try
            withLocalDeclD `k (mkConst ``True) fun _ =>
              Sym.Simp.withFreshTransientCache do
                let _ ← Sym.Simp.simp e
                throwError "nested failure"
          catch _ => pure ()
          let _ ← Sym.Simp.simp e
          pure ()
      let _ ← Sym.Simp.simp e
      pure ()
  unless (← transientCalls.get) == 3 do
    throwError "binder cache was not cleared or restored"
  unless (← persistentCalls.get) == 1 do
    throwError "persistent cache was discarded"
