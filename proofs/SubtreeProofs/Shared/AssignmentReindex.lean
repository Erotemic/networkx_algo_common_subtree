module

public import SubtreeProofs.Shared.AssignmentDuality
public import SubtreeProofs.Shared.AssignmentBiEnvelope
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


namespace SubtreeProofs.Assignment

variable {A B K : Type*} [Fintype A] [Fintype B] [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

theorem dualValue_reindex (equiv : A ≃ B) (rows columns : B → K) :
    dualValue (fun row => rows (equiv row)) (fun column => columns (equiv column)) = dualValue rows columns := by
  unfold dualValue
  rw [equiv.sum_comp rows,equiv.sum_comp columns]

theorem cost_reindex (equiv : A ≃ B) (matrix : B → B → K) (assignment : Equiv.Perm B) :
    cost (fun row column => matrix (equiv row) (equiv column)) (equiv.trans (assignment.trans equiv.symm)) = cost matrix assignment := by
  unfold cost
  simp only [Equiv.trans_apply,Equiv.apply_symm_apply]
  exact equiv.sum_comp (fun row => matrix row (assignment row))

theorem Compatible.reindex (equiv : A ≃ B) {edges : B → B → Prop} {assignment : Equiv.Perm B}
    (h : Compatible edges assignment) :
    Compatible (fun row column => edges (equiv row) (equiv column)) (equiv.trans (assignment.trans equiv.symm)) := by
  intro row
  simpa only [Equiv.trans_apply,Equiv.apply_symm_apply] using h (equiv row)

theorem FeasibleOn.reindex (equiv : A ≃ B) {edges : B → B → Prop} {matrix : B → B → K} {rows columns : B → K}
    (h : FeasibleOn edges matrix rows columns) :
    FeasibleOn (fun row column => edges (equiv row) (equiv column)) (fun row column => matrix (equiv row) (equiv column))
      (fun row => rows (equiv row)) (fun column => columns (equiv column)) :=
  fun row column he => h (equiv row) (equiv column) he

theorem BiEnvelope.reindex (equiv : A ≃ B) {initialRows initialColumns rows columns : B → K} {increment : K}
    (h : BiEnvelope initialRows initialColumns rows columns increment) :
    BiEnvelope (fun row => initialRows (equiv row)) (fun column => initialColumns (equiv column))
      (fun row => rows (equiv row)) (fun column => columns (equiv column)) increment :=
  ⟨h.nonnegative,fun row => h.row_lower (equiv row),fun row => h.row_upper (equiv row),
    fun column => h.column_lower (equiv column),fun column => h.column_upper (equiv column)⟩

theorem IsMinimumOn.reindex (equiv : A ≃ B) {edges : B → B → Prop} {matrix : B → B → K} {assignment : Equiv.Perm B}
    (h : IsMinimumOn edges matrix assignment) :
    IsMinimumOn (fun row column => edges (equiv row) (equiv column)) (fun row column => matrix (equiv row) (equiv column))
      (equiv.trans (assignment.trans equiv.symm)) := by
  refine ⟨h.1.reindex equiv,?_⟩
  intro other hOther
  let transported := equiv.symm.trans (other.trans equiv)
  have hc : Compatible edges transported := by
    intro row
    simpa only [transported,Equiv.trans_apply,Equiv.apply_symm_apply] using hOther (equiv.symm row)
  rw [cost_reindex equiv matrix assignment]
  have hh := h.2 transported hc
  have he : equiv.trans (transported.trans equiv.symm) = other := by
    ext row
    simp only [transported,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.apply_symm_apply]
  have hCost := cost_reindex equiv matrix transported
  rw [he] at hCost
  exact hh.trans_eq hCost.symm

end SubtreeProofs.Assignment

end
