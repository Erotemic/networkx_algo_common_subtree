module

public import SubtreeProofs.Shared.AssignmentRankedTrace
import Mathlib.Tactic

/-! # A ranked tight predecessor path repairs a deficient assignment optimally -/

@[expose] public section

namespace SubtreeProofs.Assignment

variable {A : Type*} [DecidableEq A]

def augmentTrace (assignment : Equiv.Perm A) (path : List A) : Equiv.Perm A :=
  path.formPerm.symm * assignment

/-- The inverse column cycle assigns each trace predecessor row to the
column that discovered it, including the free root at the last column. -/
theorem augmentTrace_predecessor (assignment : Equiv.Perm A) (predecessor : A → A) (root : A) (rest : List A)
    (ht : PredecessorTrace assignment predecessor root (assignment root) (assignment root::rest))
    (hn : (assignment root::rest).Nodup) (column : A) (hc : column ∈ assignment root::rest) :
    augmentTrace assignment (assignment root::rest) (predecessor column) = column := by
  have hf : (assignment root::rest).formPerm column = assignment (predecessor column) := by
    rw [ht.formPerm assignment predecessor root (assignment root) rest hn column hc]
    split
    · rename_i he
      rw [he]
    · rfl
  rw [augmentTrace,Equiv.Perm.mul_apply,← hf]
  exact (assignment root::rest).formPerm.symm_apply_apply column

/-- Rows whose new columns are outside the trace retain their old assignment. -/
theorem augmentTrace_away (assignment : Equiv.Perm A) (path : List A) (row : A)
    (h : augmentTrace assignment path row ∉ path) : augmentTrace assignment path row = assignment row := by
  have hf := List.formPerm_apply_of_notMem h
  have hi : path.formPerm (augmentTrace assignment path row) = assignment row :=
    path.formPerm.apply_symm_apply (assignment row)
  exact hf.symm.trans hi

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Replacing precisely the predecessor-path edges yields a compatible tight
permutation. Every retained edge is an old nonroot matching edge. -/
theorem augmentTrace_compatible_tight (edges : A → A → Prop) (matrix : A → A → K) (rows columns : A → K)
    (assignment : Equiv.Perm A) (predecessor : A → A) (root : A) (rest : List A)
    (ht : PredecessorTrace assignment predecessor root (assignment root) (assignment root::rest))
    (hn : (assignment root::rest).Nodup)
    (hOldAllowed : ∀ row, row ≠ root → edges row (assignment row))
    (hOldTight : ∀ row, row ≠ root → rows row+columns (assignment row) = matrix row (assignment row))
    (hNew : ∀ column ∈ assignment root::rest,
      edges (predecessor column) column ∧ rows (predecessor column)+columns column = matrix (predecessor column) column) :
    Compatible edges (augmentTrace assignment (assignment root::rest)) ∧
      Tight matrix rows columns (augmentTrace assignment (assignment root::rest)) := by
  have hRow : ∀ row, edges row (augmentTrace assignment (assignment root::rest) row) ∧
      rows row+columns (augmentTrace assignment (assignment root::rest) row) = matrix row (augmentTrace assignment (assignment root::rest) row) := by
    intro row
    by_cases hm : augmentTrace assignment (assignment root::rest) row ∈ assignment root::rest
    · have he : predecessor (augmentTrace assignment (assignment root::rest) row) = row :=
        (augmentTrace assignment (assignment root::rest)).injective
          (augmentTrace_predecessor assignment predecessor root rest ht hn _ hm)
      simpa only [he] using hNew _ hm
    · have he := augmentTrace_away assignment (assignment root::rest) row hm
      have hr : row ≠ root := by
        intro hh
        apply hm
        rw [he,hh]
        exact List.mem_cons_self
      rw [he]
      exact ⟨hOldAllowed row hr,hOldTight row hr⟩
  exact ⟨fun row => (hRow row).1,fun row => (hRow row).2⟩

variable [Fintype A]

/-- Decreasing positive ranks plus feasible duals and tight real predecessor
edges construct an independently minimum compatible assignment by one path
flip. No optimum or repaired matching is assumed. -/
theorem exists_ranked_augmentation (edges : A → A → Prop) (matrix : A → A → K) (rows columns : A → K)
    (assignment : Equiv.Perm A) (predecessor : A → A) (root : A) (rank : A → Nat)
    (hf : FeasibleOn edges matrix rows columns)
    (hOldAllowed : ∀ row, row ≠ root → edges row (assignment row))
    (hOldTight : ∀ row, row ≠ root → rows row+columns (assignment row) = matrix row (assignment row))
    (hStart : 0 < rank (assignment root))
    (hRank : ∀ column, 0 < rank column → predecessor column = root ∨
      0 < rank (assignment (predecessor column)) ∧ rank (assignment (predecessor column)) < rank column)
    (hEdges : ∀ column, 0 < rank column →
      edges (predecessor column) column ∧ rows (predecessor column)+columns column = matrix (predecessor column) column) :
    ∃ rest, PredecessorTrace assignment predecessor root (assignment root) (assignment root::rest) ∧
      (assignment root::rest).Nodup ∧ IsMinimumOn edges matrix (augmentTrace assignment (assignment root::rest)) ∧
      ∀ row, augmentTrace assignment (assignment root::rest) row ∉ assignment root::rest →
        augmentTrace assignment (assignment root::rest) row = assignment row := by
  obtain ⟨rest,hTrace,hNodup,hBounds⟩ := exists_ranked_predecessor_trace assignment predecessor root rank hRank (assignment root) hStart
  obtain ⟨hAllowed,hTight⟩ := augmentTrace_compatible_tight edges matrix rows columns assignment predecessor root rest hTrace hNodup
    hOldAllowed hOldTight (fun column hc => hEdges column (hBounds column hc).1)
  exact ⟨rest,hTrace,hNodup,isMinimumOn_of_feasible_tight hf hAllowed hTight,fun row hm => augmentTrace_away assignment _ row hm⟩

end SubtreeProofs.Assignment

end
