module

public import SubtreeProofs.Shared.AssignmentReduction
public import SubtreeProofs.Shared.TransposedMatchingDeletion
import Mathlib.Tactic

/-!
# Rectangular matching with zero-profit dummy columns

The production deletion family assigns rows into real columns plus one dummy
column per row. Decode only positive compatible pairs, retaining original
column labels. The specification quantifies over all independent partial
matchings, including signed weights and forbidden pairs.
-/

@[expose] public section

namespace SubtreeProofs.WeightedMatching.RectangularReduction

variable {L R K : Type*} [Fintype L] [Fintype R]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Real columns precede dummy columns, as in the production family. -/
def profit (weights : L → R → Option K) (row : L) : R ⊕ L → K
  | .inl column => max 0 ((weights row column).getD 0)
  | .inr _ => 0

noncomputable def decode (weights : L → R → Option K) (chosen : L ↪ R ⊕ L) :
    Finset (L × R) := by
  classical
  exact Finset.univ.filter (fun p => chosen p.1 = .inl p.2 ∧ 0 < (weights p.1 p.2).getD 0)

omit [IsStrictOrderedRing K] in
@[simp] theorem mem_decode (weights : L → R → Option K) (chosen : L ↪ R ⊕ L)
    (pair : L × R) : pair ∈ decode weights chosen ↔
      chosen pair.1 = .inl pair.2 ∧ 0 < (weights pair.1 pair.2).getD 0 := by
  classical
  simp [decode]

omit [IsStrictOrderedRing K] in
theorem decode_valid (weights : L → R → Option K) (chosen : L ↪ R ⊕ L) :
    Valid weights (decode weights chosen) := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro p hp hn
    have hpos := ((mem_decode weights chosen p).mp hp).2
    simp [hn] at hpos
  · intro p hp q hq hl
    apply Prod.ext hl
    have hp' := ((mem_decode weights chosen p).mp hp).1
    have hq' := ((mem_decode weights chosen q).mp hq).1
    rw [hl,hq'] at hp'
    exact Sum.inl.inj hp'.symm
  · intro p hp q hq hr
    apply Prod.ext _ hr
    have hp' := ((mem_decode weights chosen p).mp hp).1
    have hq' := ((mem_decode weights chosen q).mp hq).1
    rw [hr,← hq'] at hp'
    exact chosen.injective hp'

/-- Filtering dummy, forbidden and nonpositive pairs preserves the complete
injection profit exactly. No recurrence is used in this witness specification. -/
theorem decode_weight (weights : L → R → Option K) (chosen : L ↪ R ⊕ L) :
    weight weights (decode weights chosen) = Assignment.injectionCost (profit weights) chosen := by
  classical
  let active := Finset.univ.filter (fun row => 0 < profit weights row (chosen row))
  have hrestrict : Assignment.injectionCost (profit weights) chosen =
      ∑ row ∈ active, profit weights row (chosen row) := by
    unfold Assignment.injectionCost
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro row _ hn
    have hnot : ¬ 0 < profit weights row (chosen row) := by simpa [active] using hn
    have hnonneg : 0 ≤ profit weights row (chosen row) := by
      cases chosen row <;> simp [profit]
    exact le_antisymm (le_of_not_gt hnot) hnonneg
  rw [hrestrict]
  unfold weight
  apply Finset.sum_bij (fun p _ => p.1)
  · intro p hp
    have h := (mem_decode weights chosen p).mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [h.1]
    exact lt_of_lt_of_le h.2 (le_max_right _ _)
  · intro p hp q hq he
    exact (decode_valid weights chosen).2.1 p hp q hq he
  · intro row hr
    have hpos : 0 < profit weights row (chosen row) := (Finset.mem_filter.mp hr).2
    cases hc : chosen row with
    | inr dummy => simp [hc,profit] at hpos
    | inl column =>
      refine ⟨(row,column),(mem_decode weights chosen _).mpr ⟨hc,?_⟩,rfl⟩
      simpa [hc,profit] using hpos
  · intro p hp
    have h := (mem_decode weights chosen p).mp hp
    simp [h.1,profit,max_eq_right (le_of_lt h.2)]

/-- Reuse the existing independent partial-bijection extension. Unmatched
rows use their own dummy column; matched rows keep their original partner. -/
noncomputable def extend {weights : L → R → Option K} {pairs : Finset (L × R)}
    (hv : Valid weights pairs) : L ↪ R ⊕ L where
  toFun row := Equiv.sumComm L R (AssignmentReduction.extend hv (.inl row))
  inj' := fun _ _ h => Sum.inl.inj ((AssignmentReduction.extend hv).injective
    ((Equiv.sumComm L R).injective h))

omit [IsStrictOrderedRing K] in
theorem extend_weight {weights : L → R → Option K} {pairs : Finset (L × R)}
    (hv : Valid weights pairs) :
    Assignment.injectionCost (profit weights) (extend hv) =
      AssignmentReduction.assignmentWeight weights (AssignmentReduction.extend hv) := by
  classical
  unfold Assignment.injectionCost AssignmentReduction.assignmentWeight
  rw [Fintype.sum_sum_type]
  simp only [AssignmentReduction.profit,Finset.sum_const_zero,add_zero]
  apply Finset.sum_congr rfl
  intro row _
  change profit weights row (Equiv.sumComm L R (AssignmentReduction.extend hv (.inl row))) = _
  cases AssignmentReduction.extend hv (.inl row) <;> rfl

/-- A minimum injection for negative profits decodes to a globally maximum
independent partial matching, without any sign bound on supplied weights. -/
theorem minimum_injection_decodes {weights : L → R → Option K} (chosen : L ↪ R ⊕ L)
    (hmin : Assignment.IsMinimumInjection (fun row column => -profit weights row column) chosen) :
    IsMaximum weights (decode weights chosen) := by
  classical
  refine ⟨decode_valid weights chosen,?_⟩
  intro pairs hv
  rw [decode_weight]
  have h := hmin (extend hv)
  simp only [Assignment.injectionCost,Finset.sum_neg_distrib,neg_le_neg_iff] at h
  exact (AssignmentReduction.weight_le_extend hv).trans ((extend_weight hv).symm.le.trans h)

/-- Forbid the dummy row's real pairs, while retaining every original index. -/
def deleteRow [DecidableEq L] (weights : L → R → Option K) (removed : L) : L → R → Option K :=
  fun row column => if row = removed then none else weights row column

omit [Fintype L] [Fintype R] [IsStrictOrderedRing K] in
theorem deleteRow_cost [DecidableEq L] (weights : L → R → Option K) (removed : L) :
    (fun row column => -profit (deleteRow weights removed) row column) =
      Assignment.zeroRow (fun row column => -profit weights row column) removed := by
  funext row column
  cases column <;> by_cases hr : row = removed <;> simp [deleteRow,profit,Assignment.zeroRow,hr]

/-- The globally minimum zero-row repair decodes to an optimum excluding that
original row. Feasibility forbids the deleted endpoint, rather than assigning
it a special numeric weight in the independent matching specification. -/
theorem deleted_minimum_decodes [DecidableEq L] (weights : L → R → Option K)
    (removed : L) (chosen : L ↪ R ⊕ L)
    (hmin : Assignment.IsMinimumInjection
      (Assignment.zeroRow (fun row column => -profit weights row column) removed) chosen) :
    IsMaximum (deleteRow weights removed) (decode (deleteRow weights removed) chosen) := by
  apply minimum_injection_decodes
  rw [deleteRow_cost]
  exact hmin

end SubtreeProofs.WeightedMatching.RectangularReduction

end
