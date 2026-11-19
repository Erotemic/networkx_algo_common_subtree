module

public import SubtreeProofs.Shared.CopiedMatchingRepair
import Mathlib.Tactic

/-! # Decoding an optimum on the actual surviving copied graph -/

@[expose] public section

namespace SubtreeProofs.WeightedMatching.CopiedAssignmentReduction

variable {L R K : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

theorem profit_deleteRight_of_ne (weights : L → R → Option K) (removed : R) (row column : L ⊕ R)
    (hr : row ≠ .inr removed) (hc : column ≠ .inr removed) :
    profit (deleteRight weights removed) row column = profit weights row column := by
  cases row with
  | inl left =>
    cases column with
    | inl other => rfl
    | inr right =>
      have hn : right ≠ removed := fun he => hc (congrArg Sum.inr he)
      simp only [profit,AssignmentReduction.profit,deleteRight,hn,↓reduceIte]
  | inr right =>
    cases column with
    | inl left =>
      have hn : right ≠ removed := fun he => hr (congrArg Sum.inr he)
      simp only [profit,AssignmentReduction.profit,deleteRight,hn,↓reduceIte]
    | inr other => rfl

theorem allowed_deleteRight_of_ne (weights : L → R → Option K) (removed : R) (row column : L ⊕ R)
    (hr : row ≠ .inr removed) (hc : column ≠ .inr removed) :
    Allowed (deleteRight weights removed) row column ↔ Allowed weights row column := by
  cases row with
  | inl left =>
    cases column with
    | inl other => rfl
    | inr right =>
      have hn : right ≠ removed := fun he => hc (congrArg Sum.inr he)
      simp only [Allowed,deleteRight,hn,↓reduceIte]
  | inr right =>
    cases column with
    | inl left =>
      have hn : right ≠ removed := fun he => hr (congrArg Sum.inr he)
      simp only [Allowed,deleteRight,hn,↓reduceIte]
    | inr other => rfl

/-- Every compatible assignment for the deleted matrix fixes the removed
vertex to its zero identity edge; no cross edge remains incident to it. -/
theorem deleted_assignment_fixed (weights : L → R → Option K) (removed : R) (assignment : Equiv.Perm (L ⊕ R))
    (h : AllowedAssignment (deleteRight weights removed) assignment) : assignment (.inr removed) = .inr removed := by
  have hh := h (.inr removed)
  cases he : assignment (.inr removed) with
  | inl left => simp only [he,Allowed,deleteRight,↓reduceIte,ne_eq,not_true_eq_false,false_and] at hh
  | inr right =>
    rw [he] at hh
    change removed = right at hh
    exact congrArg Sum.inr hh.symm

theorem nonremoved_iff_of_fixed (assignment : Equiv.Perm (L ⊕ R)) (removed : R)
    (h : assignment (.inr removed) = .inr removed) (row : L ⊕ R) :
    assignment row ≠ .inr removed ↔ row ≠ .inr removed := by
  constructor
  · intro hn he
    exact hn (he ▸ h)
  · intro hn he
    exact hn (assignment.injective (he.trans h.symm))

/-- Extending a surviving permutation by a fixed zero identity edge preserves
its exact objective, with the original vertex labels retained. -/
theorem assignmentWeight_surviving (weights : L → R → Option K) (removed : R)
    (assignment : Equiv.Perm {v : L ⊕ R // v ≠ .inr removed}) :
    assignmentWeight weights (Equiv.Perm.ofSubtype assignment) =
      ∑ row, profit weights row.val (assignment row).val := by
  unfold assignmentWeight
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (.inr removed)]
  have hf : Equiv.Perm.ofSubtype assignment (.inr removed) = .inr removed :=
    Equiv.Perm.ofSubtype_apply_of_not_mem assignment (not_not_intro rfl)
  rw [hf]
  simp only [profit,AssignmentReduction.profit,add_zero,zero_add,Equiv.Perm.ofSubtype_apply_coe]

theorem assignmentWeight_deleteRight_of_fixed (weights : L → R → Option K) (removed : R)
    (assignment : Equiv.Perm (L ⊕ R)) (h : assignment (.inr removed) = .inr removed) :
    assignmentWeight (deleteRight weights removed) assignment = assignmentWeight weights assignment := by
  apply Finset.sum_congr rfl
  intro row _
  by_cases hr : row = .inr removed
  · rw [hr,h]
    rfl
  · exact profit_deleteRight_of_ne weights removed row (assignment row) hr
      ((nonremoved_iff_of_fixed assignment removed h row).mpr hr)

/-- An independently minimum compatible assignment on the induced surviving
graph decodes, in original indices, to maximum partial matchings for the
original matrix with the selected right vertex deleted. -/
theorem surviving_minimum_decodes (weights : L → R → Option K) (removed : R)
    (assignment : Equiv.Perm {v : L ⊕ R // v ≠ .inr removed})
    (h : Assignment.IsMinimumOn (fun row column => Allowed weights row.val column.val)
      (fun row column => -profit weights row.val column.val) assignment) :
    IsMaximum (deleteRight weights removed) (AssignmentReduction.decode (deleteRight weights removed) (Equiv.Perm.ofSubtype assignment)) ∧
    IsMaximum (deleteRight weights removed) (AssignmentReduction.decode (deleteRight weights removed) (Equiv.Perm.ofSubtype assignment).symm) := by
  classical
  apply dominates_allowed_decodes
  intro other ho
  have hfixed := deleted_assignment_fixed weights removed other ho
  let restricted := other.subtypePerm (p := fun v => v ≠ .inr removed) (nonremoved_iff_of_fixed other removed hfixed)
  have hr : Assignment.Compatible (fun row column : {v : L ⊕ R // v ≠ .inr removed} => Allowed weights row.val column.val) restricted := by
    intro row
    exact (allowed_deleteRight_of_ne weights removed row.val (restricted row).val row.property (restricted row).property).mp (ho row.val)
  have hi := h.2 restricted hr
  have hext : Equiv.Perm.ofSubtype restricted = other := by
    apply Equiv.Perm.ofSubtype_subtypePerm
    intro row hn he
    exact hn (he ▸ hfixed)
  have hself : Equiv.Perm.ofSubtype assignment (.inr removed) = .inr removed :=
    Equiv.Perm.ofSubtype_apply_of_not_mem assignment (not_not_intro rfl)
  rw [assignmentWeight_deleteRight_of_fixed weights removed other hfixed,
    assignmentWeight_deleteRight_of_fixed weights removed _ hself,← hext,
    assignmentWeight_surviving,assignmentWeight_surviving]
  simp only [Assignment.cost,Finset.sum_neg_distrib] at hi
  exact neg_le_neg_iff.mp hi

/-- The mathematical single-cycle repair returns an independently maximum
original-index matching for the deleted instance, while keeping every old
assignment edge outside the repair cycle. The result is existential; an
efficient executable augmenting-path search is a separate obligation. -/
theorem matched_single_cycle_decodes (weights : L → R → Option K) (assignment : Equiv.Perm (L ⊕ R)) (removed : R)
    (rows columns : L ⊕ R → K) (hfeasible : DualFeasible weights rows columns)
    (hallowed : AllowedAssignment weights assignment) (htight : DualTight weights rows columns assignment)
    (hmatched : ∃ left, (left,removed) ∈ AssignmentReduction.decode weights assignment) :
    let completed := AssignmentVertexDeletion.onRemaining assignment (.inr removed)
    let free := AssignmentVertexDeletion.freeRow assignment (.inr removed) (matched_unpaired weights assignment removed hmatched)
    ∃ replacement : Equiv.Perm {vertex : L ⊕ R // vertex ≠ .inr removed},
      let repaired := Assignment.cyclePatch completed replacement free
      IsMaximum (deleteRight weights removed) (AssignmentReduction.decode (deleteRight weights removed) (Equiv.Perm.ofSubtype repaired)) ∧
      IsMaximum (deleteRight weights removed) (AssignmentReduction.decode (deleteRight weights removed) (Equiv.Perm.ofSubtype repaired).symm) ∧
      ∀ row, ¬ (completed⁻¹*replacement).SameCycle free row → (repaired row).val = assignment row.val := by
  obtain ⟨replacement,hm,hu⟩ := matched_single_cycle_repair weights assignment removed rows columns hfeasible hallowed htight hmatched
  obtain ⟨hl,hr⟩ := surviving_minimum_decodes weights removed _ hm
  exact ⟨replacement,hl,hr,hu⟩

end SubtreeProofs.WeightedMatching.CopiedAssignmentReduction

end
