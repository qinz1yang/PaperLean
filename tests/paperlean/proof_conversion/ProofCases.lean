module
import ProofBase
public meta import Lean.PaperLean.ProofConversion
public meta import Lean.PaperLean.ProofInputs
import Lean
open Lean Meta ProofBase
universe u

theorem via {α : Type u} (x : α) (n : Nat) : Holds (target x n) := witness x n
theorem singleHit {α : Type u} (x : α) (n : Nat) : Holds (single x n) := witness x n
theorem equality {α : Type u} (x : α) (n : Nat) : source x n = target x n := witnessEq x n
theorem invalidAbstraction {α : Type u} (x : α) (n : Nat) : Holds (ignoreTarget x n) :=
  ignoreWitness x n
set_option paperlean.proofConversion false in
theorem disabled {α : Type u} (x : α) (n : Nat) : Holds (target x n) := witness x n
set_option warningAsError true in
theorem importedSorry {α : Type u} (x : α) (n : Nat) : Holds (sorryTarget x n) := witness x n
run_meta do
  for (n,cert) in [(``via,true),(``singleHit,false),(``equality,false),
      (``invalidAbstraction,false),(``disabled,false),(``importedSorry,false)] do
    let some (.thmInfo info) := (← getEnv).find? n | throwError "missing proof {n}"
    unless info.value.getLambdaBody.isAppOfArity ``Eq.mp 4 == cert do
      throwError "wrong conversion choice for {n}"

run_meta do
  let env ← getEnv
  let some (.thmInfo t) := env.find? ``disabled | throwError "missing original proof"
  let name := `replayForProofTest
  let t := {t with name, all := [name]}
  let beforeCore ← getThe Core.State
  let beforeMeta ← getThe Meta.State
  let r ← PaperLean.ProofConversion.optimize t
  let afterCore ← getThe Core.State
  let afterMeta ← getThe Meta.State
  unless (unsafe ptrEq beforeCore afterCore) && (unsafe ptrEq beforeMeta afterMeta) do
    throwError "speculative conversion changed the caller's Core/Meta state"
  unless !Expr.equal r.value t.value && Expr.equal r.type t.type && r.levelParams == t.levelParams do
    throwError "missing validated conversion or changed theorem signature"
  let declined ← withOptions (maxRecDepth.set · 1) <| PaperLean.ProofConversion.optimize t
  unless Expr.equal declined.value t.value do throwError "low-limit conversion did not fall back"
  match env.toKernelEnv.addDeclCore 0 4000 (.thmDecl declined) none with
  | .ok _ => pure ()
  | .error e => throwError "original theorem failed after fallback: {e.toMessageData (← getOptions)}"
  let tk ← IO.CancelToken.new
  tk.set
  let stopped ← try
    discard <| withTheReader Core.Context (fun ctx => {ctx with cancelTk? := some tk}) <|
      PaperLean.ProofConversion.optimize t
    pure false
  catch e =>
    if e.isInterrupt then pure true else throw e
  unless stopped do throwError "proof conversion swallowed cancellation"

run_meta do
  let env ← getEnv
  let n := `registryVisibilityWitness
  let d : DefinitionVal := {
    name := n, levelParams := [], type := mkConst ``Nat, value := mkNatLit 0
    hints := .abbrev, safety := .safe, all := [n] }
  unless (PaperLean.ProofInputs.lookup env n (privateKernel := true)).isNone do
    throwError "unexpected input in original branch"
  let branch ← PaperLean.ProofInputs.record env (.defnDecl d) (← getOptions) false
  unless (PaperLean.ProofInputs.lookup (branch.setExporting false) n).isSome &&
      (PaperLean.ProofInputs.lookup (branch.setExporting true) n).isNone &&
      (PaperLean.ProofInputs.lookup (branch.setExporting true) n (privateKernel := true)).isSome &&
      (PaperLean.ProofInputs.lookup env n (privateKernel := true)).isNone do
    throwError "local registry leaked across branches or visibility boundaries"
  let exported ← PaperLean.ProofInputs.record env (.defnDecl d) (← getOptions) true
  unless (PaperLean.ProofInputs.lookup (exported.setExporting true) n).isSome do
    throwError "exported definition missing from its branch"
