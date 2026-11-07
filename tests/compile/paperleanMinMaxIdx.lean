import Init

-- Independent fold over indexed input elements.
private def oracle (prefer : Nat → Nat → Bool) (xs : List Nat) : Option Nat :=
  (xs.zipIdx.foldl (fun best entry =>
    match best with
    | none => some entry
    | some incumbent => if prefer incumbent.1 entry.1 then best else some entry)
    (none : Option (Nat × Nat))).map Prod.snd

private def words : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (words n).flatMap fun xs => (List.range 4).map (· :: xs)

-- Keep the reference loop independent of the public implementation.
@[noinline, nospecialize] private def frozenMin? (ord : LE β) (d : @DecidableLE β ord)
    (f : α → β) (xs : List α) : Option Nat :=
  match xs with
  | [] => none
  | x :: xs => some (go x 0 1 xs)
where
  go (x : α) (i j : Nat) : List α → Nat
    | [] => i
    | y :: ys =>
      if @decide (ord.le (f x) (f y)) (d (f x) (f y)) then go x i (j + 1) ys
      else go y j (j + 1) ys

private def requireIndex (label : String) (xs : List Nat) (got want : Option Nat) : IO Unit := do
  unless got == want do
    throw <| IO.userError s!"{label} on {xs}: got {repr got}, expected {repr want}"

-- All five runtime operands (including the relation's decider) are explicit at the
-- public and reference calls. This generic boundary keeps the fixture's source simple
-- even when multiple unrelated relations on Nat occur in the same test program.
@[noinline, nospecialize] private def checkOrder (label : String) (ord : LE β)
    (d : @DecidableLE β ord) (f : Nat → β) (prefer : Nat → Nat → Bool) (xs : List Nat) : IO Unit := do
  let rev : LE β := ⟨fun a b => ord.le b a⟩
  let revDec : @DecidableLE β rev := fun a b => d b a
  let lo := oracle prefer xs
  let hi := oracle (fun a b => prefer b a) xs
  requireIndex s!"{label} frozen min" xs (frozenMin? ord d f xs) lo
  requireIndex s!"{label} frozen reversed min" xs (frozenMin? rev revDec f xs) hi
  requireIndex s!"{label} public min?" xs (@List.minIdxOn? β Nat ord d f xs) lo
  requireIndex s!"{label} public max?" xs (@List.maxIdxOn? β Nat ord d f xs) hi
  requireIndex s!"{label} public reversed min?" xs (@List.minIdxOn? β Nat rev revDec f xs) hi
  match xs with
  | [] => pure ()
  | x :: ys =>
    have h : x :: ys ≠ [] := by simp
    requireIndex s!"{label} public min" (x :: ys) (some (@List.minIdxOn β Nat ord d f (x :: ys) h)) lo
    requireIndex s!"{label} public max" (x :: ys) (some (@List.maxIdxOn β Nat ord d f (x :: ys) h)) hi

private def score (n : Nat) := (n + 1) % 3
private abbrev ordinary : LE Nat := inferInstance
@[instance_reducible] private def ordinaryDec : @DecidableLE Nat ordinary := fun a b => inferInstanceAs (Decidable (a ≤ b))
@[instance_reducible] private def different : LE Nat := ⟨fun a b => a % 3 ≠ b % 3⟩
@[instance_reducible] private def differentDec : @DecidableLE Nat different :=
  fun a b => inferInstanceAs (Decidable (a % 3 ≠ b % 3))
-- Unlike inequality of residues, this non-order distinguishes forward from reversed calls.
@[instance_reducible] private def cyclic : LE Nat := ⟨fun a b => (a + 1) % 3 = b % 3⟩
@[instance_reducible] private def cyclicDec : @DecidableLE Nat cyclic :=
  fun a b => inferInstanceAs (Decidable ((a + 1) % 3 = b % 3))

private def check (xs : List Nat) : IO Unit := do
  checkOrder "ordinary" ordinary ordinaryDec score (fun a b => decide (score a ≤ score b)) xs
  checkOrder "different residues" different differentDec score
    (fun a b => decide (score a % 3 ≠ score b % 3)) xs
  checkOrder "cyclic" cyclic cyclicDec score
    (fun a b => decide ((score a + 1) % 3 = score b % 3)) xs

example (f : α → Nat) (x : α) : [x].minIdxOn f (by simp) = 0 := rfl
example : ([5, 2, 2, 7] : List Nat).minIdxOn? id = some 1 := rfl
example : ([5, 7, 7, 2] : List Nat).maxIdxOn? id = some 1 := rfl

def main : IO Unit := do
  for n in List.range 7 do
    for xs in words n do check xs
  IO.println "min/max index oracle passed"
