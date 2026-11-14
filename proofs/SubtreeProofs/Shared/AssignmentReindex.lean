module

public import SubtreeProofs.Shared.AssignmentDuality
import Mathlib.Tactic

/-!
# Assignment reduction under an independent index equivalence

Mathlib's permutation congruence transports a complete assignment to the
left/right sum indexing of the partial-matching reduction. Feasible/tight
potentials and exact cost transport give both maximum-witness correctness
and its exact negated-cost weight.
-/

@[expose] public section

namespace SubtreeProofs.Assignment

variable {L R A K : Type*} [Fintype L] [Fintype R] [Fintype A]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A concrete-index assignment with the dummy costs decodes, under any
index equivalence, to a maximum partial matching with exact cost/weight. -/
theorem reindexed_assignment_decodes (weights : L → R → Option K) (indices : (L ⊕ R) ≃ A)
    (matrix : A → A → K) (rows columns : A → K) (assignment : Equiv.Perm A)
    (hcost : ∀ row col, matrix (indices row) (indices col) = -WeightedMatching.AssignmentReduction.profit weights row col)
    (hfeasible : Feasible matrix rows columns) (htight : Tight matrix rows columns assignment) :
    WeightedMatching.IsMaximum weights (WeightedMatching.AssignmentReduction.decode weights (indices.permCongr.symm assignment)) ∧
      WeightedMatching.weight weights (WeightedMatching.AssignmentReduction.decode weights (indices.permCongr.symm assignment)) =
        -cost matrix assignment := by
  let decodedAssignment := indices.permCongr.symm assignment
  have happly : ∀ row, indices (decodedAssignment row) = assignment (indices row) := by
    intro row
    simp only [decodedAssignment,Equiv.permCongr_symm_apply,Equiv.apply_symm_apply]
  have hf : Feasible (fun row col => 0-WeightedMatching.AssignmentReduction.profit weights row col)
      (fun row => rows (indices row)) (fun col => columns (indices col)) := by
    intro row col
    have h := hfeasible (indices row) (indices col)
    rw [hcost] at h
    simpa only [zero_sub] using h
  have ht : Tight (fun row col => 0-WeightedMatching.AssignmentReduction.profit weights row col)
      (fun row => rows (indices row)) (fun col => columns (indices col)) decodedAssignment := by
    intro row
    have h := htight (indices row)
    rw [← happly row,hcost] at h
    simpa only [zero_sub] using h
  refine ⟨tight_assignment_decodes weights 0 _ _ decodedAssignment hf ht,?_⟩
  rw [WeightedMatching.AssignmentReduction.decode_weight]
  have hsum : cost matrix assignment = -WeightedMatching.AssignmentReduction.assignmentWeight weights decodedAssignment := by
    unfold cost
    rw [← Equiv.sum_comp indices (fun row => matrix row (assignment row))]
    calc
      _ = ∑ row : L ⊕ R, -WeightedMatching.AssignmentReduction.profit weights row (decodedAssignment row) := by
        apply Finset.sum_congr rfl
        intro row _
        rw [← happly row,hcost]
      _ = _ := by rw [Finset.sum_neg_distrib]; rfl
  rw [hsum,neg_neg]

end SubtreeProofs.Assignment

end
