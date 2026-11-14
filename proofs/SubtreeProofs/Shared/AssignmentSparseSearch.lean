module

public import SubtreeProofs.Shared.AssignmentSparsePotentials
import Mathlib.Tactic

/-! # Alternating cut growth for a single missing assignment edge

Complete the deficient matching by the temporary free-row/free-column edge.
The remaining permutation edges are real and tight. Before the search reaches
the temporary edge's column, its selected rows consist exactly of the free
root and the inverse images of selected matched columns.
-/

@[expose] public section

namespace SubtreeProofs.Assignment

variable {A : Type*} [DecidableEq A]

def searchRows (assignment : Equiv.Perm A) (root : A) (columns : Finset A) : Finset A :=
  insert root (columns.image assignment.symm)

@[simp] theorem mem_searchRows (assignment : Equiv.Perm A) (root row : A) (columns : Finset A) :
    row ∈ searchRows assignment root columns ↔ row = root ∨ assignment row ∈ columns := by
  simp only [searchRows,Finset.mem_insert,Finset.mem_image]
  constructor
  · rintro (he | ⟨column,hColumn,he⟩)
    · exact Or.inl he
    · right
      subst row
      simpa only [Equiv.apply_symm_apply] using hColumn
  · rintro (he | hColumn)
    · exact Or.inl he
    · exact Or.inr ⟨assignment row,hColumn,assignment.symm_apply_apply row⟩

theorem searchRows_card (assignment : Equiv.Perm A) (root : A) (columns : Finset A)
    (hfree : assignment root ∉ columns) :
    (searchRows assignment root columns).card = columns.card+1 := by
  have hr : root ∉ columns.image assignment.symm := by
    intro hm
    obtain ⟨column,hc,he⟩ := Finset.mem_image.mp hm
    have hh := congrArg assignment he
    rw [Equiv.apply_symm_apply] at hh
    exact hfree (hh ▸ hc)
  rw [searchRows,Finset.card_insert_of_notMem hr,Finset.card_image_of_injective _ assignment.symm.injective]

theorem searchRows_matched_iff (assignment : Equiv.Perm A) (root row : A) (columns : Finset A) (hn : row ≠ root) :
    row ∈ searchRows assignment root columns ↔ assignment row ∈ columns := by
  simp only [mem_searchRows,hn,false_or]

/-- An unexplored column's matched row is fresh unless this is the free
target column, which is exactly the augmenting-path termination case. -/
theorem search_next_row_fresh (assignment : Equiv.Perm A) (root column : A) (columns : Finset A)
    (hc : column ∉ columns) (hf : column ≠ assignment root) :
    assignment.symm column ∉ searchRows assignment root columns := by
  rw [mem_searchRows,Equiv.apply_symm_apply,not_or]
  refine ⟨?_,hc⟩
  intro he
  exact hf ((assignment.apply_symm_apply column).symm.trans (congrArg assignment he))

theorem searchRows_insert (assignment : Equiv.Perm A) (root column : A) (columns : Finset A) :
    searchRows assignment root (insert column columns) = insert (assignment.symm column) (searchRows assignment root columns) := by
  simp only [searchRows,Finset.image_insert,Finset.insert_comm]

/-- Each nonterminal extension increases selected rows and columns by one,
retains the free target outside the cut and preserves the one-row deficit. -/
theorem search_cut_grows (assignment : Equiv.Perm A) (root column : A) (columns : Finset A)
    (hfree : assignment root ∉ columns) (hc : column ∉ columns) (hf : column ≠ assignment root) :
    assignment root ∉ insert column columns ∧
    (insert column columns).card = columns.card+1 ∧
    (searchRows assignment root (insert column columns)).card = (searchRows assignment root columns).card+1 ∧
    (searchRows assignment root (insert column columns)).card = (insert column columns).card+1 := by
  have hn : assignment root ∉ insert column columns := by simp only [Finset.mem_insert,not_or]; exact ⟨Ne.symm hf,hfree⟩
  refine ⟨hn,Finset.card_insert_of_notMem hc,?_,searchRows_card assignment root _ hn⟩
  rw [searchRows_insert,Finset.card_insert_of_notMem (search_next_row_fresh assignment root column columns hc hf)]

variable [Fintype A]

theorem search_cut_card_lt (assignment : Equiv.Perm A) (root : A) (columns : Finset A)
    (hfree : assignment root ∉ columns) : columns.card < Fintype.card A := by
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _,by
    intro he
    exact hfree (he ▸ Finset.mem_univ _)⟩)

/-- The finite complement of selected columns strictly decreases at every
extension. This is the termination measure for the actual search caller. -/
theorem search_cut_measure_decreases (assignment : Equiv.Perm A) (root column : A) (columns : Finset A)
    (hfree : assignment root ∉ columns) (hc : column ∉ columns) :
    Fintype.card A-(insert column columns).card < Fintype.card A-columns.card := by
  have hb := search_cut_card_lt assignment root columns hfree
  rw [Finset.card_insert_of_notMem hc]
  omega

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The selected-row construction locks both endpoints of every actual
matched edge together. Every such old tight edge therefore survives the
potential update; only the temporary root edge is excluded. -/
theorem search_adjust_preserves_matching (assignment : Equiv.Perm A) (root : A) (selectedColumns : Finset A)
    (matrix : A → A → K) (rows columns : A → K) (delta : K)
    (ht : ∀ row, row ≠ root → rows row+columns (assignment row) = matrix row (assignment row)) :
    ∀ row, row ≠ root →
      adjustRows rows (searchRows assignment root selectedColumns) delta row+
        adjustColumns columns selectedColumns delta (assignment row) = matrix row (assignment row) := by
  intro row hn
  exact adjust_preserves_tight_edge matrix rows columns _ _ delta row (assignment row) (ht row hn)
    (searchRows_matched_iff assignment root row selectedColumns hn)

/-- The independent sparse search always has an attained allowed adjustment.
It preserves all actual matching edges' tightness, creates a new tight edge,
and either reaches the free target or identifies a fresh matched row. -/
theorem exists_search_adjustment (edges : A → A → Prop) (matrix : A → A → K)
    (assignment : Equiv.Perm A) (root : A) (selectedColumns : Finset A) (rows columns : A → K)
    (hfree : assignment root ∉ selectedColumns) (hf : FeasibleOn edges matrix rows columns)
    (ht : ∀ row, row ≠ root → rows row+columns (assignment row) = matrix row (assignment row))
    (he : ∃ replacement : Equiv.Perm A, Compatible edges replacement) :
    ∃ delta row column, row ∈ searchRows assignment root selectedColumns ∧ column ∉ selectedColumns ∧ edges row column ∧
      0 ≤ delta ∧ delta = matrix row column-rows row-columns column ∧
      FeasibleOn edges matrix (adjustRows rows (searchRows assignment root selectedColumns) delta)
        (adjustColumns columns selectedColumns delta) ∧
      (∀ matched, matched ≠ root →
        adjustRows rows (searchRows assignment root selectedColumns) delta matched+
          adjustColumns columns selectedColumns delta (assignment matched) = matrix matched (assignment matched)) ∧
      adjustRows rows (searchRows assignment root selectedColumns) delta row+
        adjustColumns columns selectedColumns delta column = matrix row column ∧
      (column = assignment root ∨ assignment.symm column ∉ searchRows assignment root selectedColumns) := by
  obtain ⟨delta,row,column,hRow,hColumn,hEdge,hSlack,hDelta,hCut,hFeasible,hTight⟩ :=
    exists_cut_adjustment_on edges matrix rows columns (searchRows assignment root selectedColumns) selectedColumns
      (searchRows_card assignment root selectedColumns hfree) hf he
  refine ⟨delta,row,column,hRow,hColumn,hEdge,hDelta,hSlack,hFeasible,
    search_adjust_preserves_matching assignment root selectedColumns matrix rows columns delta ht,hTight,?_⟩
  by_cases hc : column = assignment root
  · exact Or.inl hc
  · exact Or.inr (search_next_row_fresh assignment root column selectedColumns hColumn hc)

end SubtreeProofs.Assignment

end
