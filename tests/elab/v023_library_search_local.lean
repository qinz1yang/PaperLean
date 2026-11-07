import Lean
import Lean.Elab.Parallel

open Lean Meta

theorem v023LocalStar (P : Prop) (h : P) : P := h

run_meta do
  let tasks ← (List.range 4).mapM fun _ => MetaM.asTask' do
    let _ ← LibrarySearch.libSearchFindDecls (mkConst ``True)
    LibrarySearch.getStarLemmas
  let mut previous : Option (Array (Name × LibrarySearch.DeclMod)) := none
  for task in tasks do
    let xs ← task.get
    unless (xs.filter (·.1 == ``v023LocalStar)).size == 1 do
      throwError "concurrent initialization duplicated local stars"
    if let some prior := previous then
      unless xs == prior do throwError "concurrent queries disagreed"
    previous := some xs

run_meta do
  let mut previous : Option (Array (Name × LibrarySearch.DeclMod)) := none
  for _ in [:4] do
    let _ ← LibrarySearch.libSearchFindDecls (mkConst ``True)
    let xs ← LibrarySearch.getStarLemmas
    unless (xs.filter (·.1 == ``v023LocalStar)).size == 1 do
      throwError "local star lemma was duplicated"
    if let some prior := previous then
      unless xs == prior do throwError "unchanged search changed candidate order"
    previous := some xs
  let env ← getEnv
  let n := `v023TransientStar
  let type := mkForall `P .default (mkSort .zero)
    (mkForall `h .default (.bvar 0) (.bvar 1))
  let value := mkLambda `P .default (mkSort .zero)
    (mkLambda `h .default (.bvar 0) (.bvar 0))
  try
    addDecl (.thmDecl { name := n, levelParams := [], type, value })
    let _ ← LibrarySearch.libSearchFindDecls (mkConst ``True)
    unless (← LibrarySearch.getStarLemmas).any (·.1 == n) do
      throwError "new local theorem is absent"
  finally
    setEnv env
  let _ ← LibrarySearch.libSearchFindDecls (mkConst ``True)
  if (← LibrarySearch.getStarLemmas).any (·.1 == n) then
    throwError "backtracked theorem survived in imported cache"
