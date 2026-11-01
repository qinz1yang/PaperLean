/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
`lean --run reverse_abi.lean <lib/lean> <out>` writes what compiled code of other modules can rely on
about each declaration of the toolchain at `<lib/lean>`, private and generated ones included (from
the `.ir` part of each module, or the only part of a file that is no `module`), one line each:
- `ir <name> <parameters> : <result>`, its IR signature with the borrow flags;
- `impure <name> <parameters> : <result>`, its impure LCNF signature;
- `calls <name> <hash>` for generated declarations (`_at_`, `_lam_`, `_redArg`, `unsafe_`,
  `_boxed`…), of what it calls: a generated declaration of official Lean that PaperLean has under the
  same name and signature could be another specialization (a function of the decl's callees, with
  `_closed_` terms not told apart, as their numbers do not say what they are).

`tests/paperlean/reverse_abi.sh` compares official Lean's lines with PaperLean's.
-/

open Lean Compiler LCNF

def typeStr (t : IR.IRType) : String := toString (format t)

def paramStr (borrow : Bool) (ty : String) : String :=
  if borrow then s!"@&{ty}" else ty

def isGenerated (n : Name) : Bool :=
  n.components.any fun
    | .str _ s => s == "_at_" || s == "_redArg" || s == "_boxed" || s.startsWith "_lam_" ||
      s.startsWith "unsafe_" || s.startsWith "spec_" || s.startsWith "_elam_"
    | _ => false

partial def callees (acc : Array Name) : IR.FnBody → Array Name
  | .vdecl _ _ e b => callees (match e with | .fap c _ | .pap c _ => acc.push c | _ => acc) b
  | .jdecl _ _ v b => callees (callees acc v) b
  | .case _ _ _ cs => cs.foldl (fun acc a => callees acc a.body) acc
  | b => if b.isTerminal then acc else callees acc b.body

/-- `n` with the number of a `_closed_` component dropped. -/
def closedNormalized : Name → Name
  | .str p s => .str (closedNormalized p) (if s.startsWith "_closed_" then "_closed" else s)
  | .num p k => .num (closedNormalized p) k
  | .anonymous => .anonymous

def callsHash (body : IR.FnBody) : UInt64 :=
  let names := (callees #[] body).map (toString <| closedNormalized ·)
  names.qsort (· < ·) |>.foldl (fun h s => mixHash h (hash s)) 7

unsafe def irLines (h : IO.FS.Handle) (d : IR.Decl) : IO Unit := do
  let ps := " ".intercalate (d.params.map fun p => paramStr p.borrow (typeStr p.ty)).toList
  h.putStrLn s!"ir {d.name} {ps} : {typeStr d.resultType}"
  if let .fdecl (body := b) .. := d then
    if isGenerated d.name then
      h.putStrLn s!"calls {d.name} {callsHash b}"

unsafe def impureLine (h : IO.FS.Handle) (s : Signature .impure) : IO Unit := do
  let ps := " ".intercalate (s.params.map fun p => paramStr p.borrow (toString p.type)).toList
  h.putStrLn s!"impure {s.name} {ps} : {s.type}"

def extOf (n : Name) : String := match n with | .str _ s => s | _ => ""

partial def oleans (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut r := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then r := r ++ (← oleans e.path)
    else if e.path.extension == some "olean" then r := r.push e.path
  return r

unsafe def main (args : List String) : IO Unit := do
  let root : System.FilePath := args[0]!
  let h ← IO.FS.Handle.mk args[1]! .write
  for f in ← oleans root do
    -- (the roots of executables are not `module`s: they have no `.ir` part)
    let d ← if ← (f.withExtension "ir").pathExists then
        let ds ← readModuleDataParts #[f.withExtension "ir.sig", f.withExtension "ir"]
        let some (d, _) := ds[1]? | throw <| IO.userError s!"ir parts of {f}"
        pure d
      else pure (← readModuleData f).1
    for (n, es) in d.entries do
      for e in es do
        match extOf n with
        | "declMapExt" => irLines h (unsafeCast e)
        | "impureSigExt" => impureLine h (unsafeCast e)
        | _ => pure ()
