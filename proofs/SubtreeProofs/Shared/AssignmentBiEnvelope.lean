module

public import SubtreeProofs.Shared.AssignmentSparsePotentials
import Mathlib.Tactic

/-! # Potential envelopes with nonzero initial values on both sides

The copied graph initialization in 2016 Lemma 5 assigns nonzero potentials
to left vertices and their copies. A zero-column baseline cannot describe
that state. These bounds track both original sides explicitly.
-/

@[expose] public section

namespace SubtreeProofs.Assignment

variable {A K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

structure BiEnvelope (initialRows initialColumns rows columns : A → K) (increment : K) : Prop where
  nonnegative : 0 ≤ increment
  row_lower : ∀ row, initialRows row ≤ rows row
  row_upper : ∀ row, rows row ≤ initialRows row + increment
  column_lower : ∀ column, initialColumns column - increment ≤ columns column
  column_upper : ∀ column, columns column ≤ initialColumns column

omit [IsStrictOrderedRing K] in
theorem biEnvelope_initial (initialRows initialColumns : A → K) :
    BiEnvelope initialRows initialColumns initialRows initialColumns 0 := by
  constructor <;> simp

variable [DecidableEq A]

theorem BiEnvelope.adjust {initialRows initialColumns rows columns : A → K} {increment : K}
    (h : BiEnvelope initialRows initialColumns rows columns increment)
    (selectedRows selectedColumns : Finset A) (delta : K) (hd : 0 ≤ delta) :
    BiEnvelope initialRows initialColumns (adjustRows rows selectedRows delta)
      (adjustColumns columns selectedColumns delta) (increment+delta) := by
  refine ⟨add_nonneg h.nonnegative hd,?_,?_,?_,?_⟩
  · intro row
    have hl := h.row_lower row
    by_cases hr : row ∈ selectedRows <;> simp only [adjustRows,hr,↓reduceIte] <;> linarith
  · intro row
    have hu := h.row_upper row
    by_cases hr : row ∈ selectedRows <;> simp only [adjustRows,hr,↓reduceIte] <;> linarith
  · intro column
    have hl := h.column_lower column
    by_cases hc : column ∈ selectedColumns <;> simp only [adjustColumns,hc,↓reduceIte] <;> linarith
  · intro column
    have hu := h.column_upper column
    by_cases hc : column ∈ selectedColumns <;> simp only [adjustColumns,hc,↓reduceIte] <;> linarith

variable [Fintype A]

omit [DecidableEq A] in
/-- Separate cost and initial-potential bounds retain the sharper budget for
nonpositive copied-graph costs. No forbidden pair needs a finite cost. -/
theorem total_increment_bound_both_on {edges : A → A → Prop} {matrix : A → A → K}
    (initialRows initialColumns finalRows finalColumns : A → K) (bound costUpper increment : K)
    (hr : ∀ row, -bound ≤ initialRows row) (hc : ∀ column, -bound ≤ initialColumns column)
    (hcost : ∀ row column, edges row column → matrix row column ≤ costUpper)
    (hf : FeasibleOn edges matrix finalRows finalColumns)
    (he : ∃ assignment : Equiv.Perm A, Compatible edges assignment)
    (haccount : dualValue finalRows finalColumns = dualValue initialRows initialColumns+increment) :
    increment ≤ (Fintype.card A : K)*(costUpper+2*bound) := by
  have hfinal := dualValue_le_card_mul_on costUpper hf hcost he
  have hrows := Finset.sum_le_sum (s := (Finset.univ : Finset A)) (fun row _ => hr row)
  have hcolumns := Finset.sum_le_sum (s := (Finset.univ : Finset A)) (fun column _ => hc column)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_neg] at hrows hcolumns
  unfold dualValue at haccount hfinal
  nlinarith

theorem ideal_adjustment_increment_bound_both_on {edges : A → A → Prop} {matrix : A → A → K}
    (initialRows initialColumns rows columns : A → K) (selectedRows selectedColumns : Finset A)
    (increment delta bound costUpper : K)
    (hr : ∀ row, -bound ≤ initialRows row) (hc : ∀ column, -bound ≤ initialColumns column)
    (hcost : ∀ row column, edges row column → matrix row column ≤ costUpper)
    (hf : FeasibleOn edges matrix rows columns) (hd : 0 ≤ delta)
    (hcut : ∀ row ∈ selectedRows, ∀ column, column ∉ selectedColumns → edges row column →
      delta ≤ matrix row column-rows row-columns column)
    (hcard : selectedRows.card = selectedColumns.card+1)
    (he : ∃ assignment : Equiv.Perm A, Compatible edges assignment)
    (haccount : dualValue rows columns = dualValue initialRows initialColumns+increment) :
    increment+delta ≤ (Fintype.card A : K)*(costUpper+2*bound) := by
  apply total_increment_bound_both_on initialRows initialColumns (adjustRows rows selectedRows delta)
    (adjustColumns columns selectedColumns delta) bound costUpper (increment+delta) hr hc hcost
    (adjust_feasible_on hf hd hcut) he
  rw [adjust_dualValue_one rows columns selectedRows selectedColumns delta hcard,haccount]
  ring

/-- Removing a coordinate removes exactly its two potential contributions. -/
theorem dualValue_restrict_ne (rows columns : A → K) (removed : A) :
    dualValue (fun row : {a : A // a ≠ removed} => rows row.val)
      (fun column : {a : A // a ≠ removed} => columns column.val) =
      dualValue rows columns-rows removed-columns removed := by
  classical
  have hr := Fintype.sum_eq_add_sum_subtype_ne rows removed
  have hc := Fintype.sum_eq_add_sum_subtype_ne columns removed
  unfold dualValue
  rw [hr,hc]
  ring

/-- Deleting a zero-cost identity coordinate preserves a valid warm-start
envelope and exact accounting. The baseline has zero at the removed vertex
on both sides, as in the paper's right-vertex/copy deletion. -/
theorem BiEnvelope.delete {initialRows initialColumns rows columns : A → K} {increment : K}
    (h : BiEnvelope initialRows initialColumns rows columns increment) (removed : A)
    (hr : initialRows removed = 0) (hc : initialColumns removed = 0)
    (hidentity : rows removed+columns removed ≤ 0)
    (haccount : dualValue rows columns = dualValue initialRows initialColumns+increment) :
    BiEnvelope (fun row : {a : A // a ≠ removed} => initialRows row.val)
      (fun column : {a : A // a ≠ removed} => initialColumns column.val)
      (fun row : {a : A // a ≠ removed} => rows row.val)
      (fun column : {a : A // a ≠ removed} => columns column.val)
      (increment-(rows removed+columns removed)) ∧
    dualValue (fun row : {a : A // a ≠ removed} => rows row.val)
      (fun column : {a : A // a ≠ removed} => columns column.val) =
      dualValue (fun row : {a : A // a ≠ removed} => initialRows row.val)
        (fun column : {a : A // a ≠ removed} => initialColumns column.val)+
        (increment-(rows removed+columns removed)) := by
  constructor
  · refine ⟨by linarith [h.nonnegative],fun row => h.row_lower row.val,?_,?_,fun column => h.column_upper column.val⟩
    · intro row
      linarith [h.row_upper row.val]
    · intro column
      linarith [h.column_lower column.val]
  · rw [dualValue_restrict_ne,dualValue_restrict_ne,hr,hc,haccount]
    ring

end SubtreeProofs.Assignment

end
