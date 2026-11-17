import SubtreeProofs.Complexity.EditDistance.Work
import SubtreeProofs.Complexity.Paper2004.MemoWork

namespace MemoWorkTests

open SubtreeProofs.Complexity.Memo

private def eventCost (result : EStateM.Result Unit (EvalState QueryKey Storage) (List Nat)) :
    Option Nat :=
  match result with
  | .error _ _ => none
  | .ok _ final => some (Event.totalWork 0 0 final.events)

private def totalCost (result : Nat × EStateM.Result Unit (EvalState QueryKey Storage) (List Nat)) :
    Option Nat := (result.1 + ·) <$> eventCost result.2

open SubtreeProofs.Complexity.EditDistance in
example : totalCost (runList ['x'] ['y'] [(0, 0)]) = some 13 := by decide +kernel

open SubtreeProofs.Complexity.EditDistance in
example : totalCost (runDense ['x'] ['y'] [(0, 0)]) = some 34 := by decide +kernel

open SubtreeProofs.Complexity.EditDistance in
example : totalCost (runDense ['x'] ['y'] []) = some 5 := by decide +kernel

open SubtreeProofs.Complexity.EditDistance in
example : totalCost (runDense [] ['a', 'b'] [(0, 0)]) = some 10 := by decide +kernel

open SubtreeProofs.Complexity.EditDistance in
example : ∃ final, (runDense ['x'] ['y'] [(0, 0)]).2 = .ok [1] final ∧
    (runDense ['x'] ['y'] [(0, 0)]).1 + Event.totalWork 0 0 final.events ≤ 34 := by
  obtain ⟨final, hr, _, hw⟩ := dense_weighted_work_spec ['x'] ['y'] [(0, 0)] 0 0
  exact ⟨final, by simpa [value, distance] using hr, by simpa using hw⟩

private def constantProblem : Problem (Fin 3) Nat where
  value := Fin.val
  body := fun key => .done key.val
  rank := fun _ => 0
  body_correct := fun _ => rfl
  requests_decrease := by intro key child hm; simp at hm

private def listOps := (ListCache.ops : CacheOps (Fin 3) Nat (List (Fin 3 × Nat)))
private def warm : List (Fin 3 × Nat) := [(0, 0), (1, 1)]

-- Unrelated warm entries contribute scan cost despite lying outside the
-- one-key reachable envelope. Counting only missing keys would underprice it.
example : eventCost (evalRoots listOps constantProblem.body 1 [2] ⟨warm, []⟩) = some 3 := by
  decide +kernel

example : ¬ (listOps.read 2 warm).2 ≤ ({2} : Finset (Fin 3)).card := by decide +kernel

example : ∃ final, evalRoots listOps constantProblem.body 1 [2] ⟨warm, []⟩ = .ok [2] final ∧
    TraceInvariant listOps constantProblem warm final ∧ Event.totalWork 0 0 final.events ≤ 4 := by
  have hs : listOps.Sound constantProblem.value warm := by
    intro key stored hm
    fin_cases key <;> simp_all [listOps, ListCache.ops, warm, constantProblem, List.lookup]
  have hfilter : (({2} : Finset (Fin 3)).filter fun key => key ≠ 0 ∧ key ≠ 1).card = 1 := by
    decide +kernel
  simpa [listOps, ListCache.ops, ListCache.workModel, warm, constantProblem, hfilter] using
    roots_work_envelope listOps constantProblem ListCache.workModel {2} (fun _ => 0) 0 0 0
      (by intro key _ child hm; simp [constantProblem] at hm)
      (by simp [constantProblem]) (by simp [constantProblem]) 1 [2] warm
      (by change (warm.map Prod.fst).Nodup; decide +kernel) hs (by simp [constantProblem]) (by simp)

-- Same values/cache behavior, but one additional declared read unit. The old
-- empty-list primitive budget fails even though functional laws still hold.
private def extraReadOps : CacheOps (Fin 3) Nat (List (Fin 3 × Nat)) :=
  { listOps with
    read := fun key storage =>
      let found := ListCache.read key storage
      (found.1, found.2 + 1)
    read_correct := fun key storage _ => ListCache.read_value key storage }

example : (extraReadOps.read 0 []).1 = (listOps.read 0 []).1 := rfl

example : ¬ (extraReadOps.read 0 []).2 ≤
    (ListCache.workModel : WorkModel listOps).readCost 0 := by decide +kernel

-- Dense pair lookup includes encoding; the old one-cell-only budget fails.
example : ¬ ((DirectCache.productOps 2 2 Nat).read (0, 0) #[]).2 ≤ 1 := by decide +kernel

end MemoWorkTests
