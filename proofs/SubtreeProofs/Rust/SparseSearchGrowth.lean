module

public import SubtreeProofs.Rust.SparseSearchTightness
import Mathlib.Tactic

/-! # Selected-set and visit accounting after actual sparse search writes -/

@[expose] public section

open Aeneas Aeneas.Std
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseSearch

open SparseCut

structure CutFrame (cost : Slice (alloc.vec.Vec (Option I64))) (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost)
    (oldRows oldColumns newRows newColumns : alloc.vec.Vec Bool) (next : Usize) (searching : Bool) (column : Vertex cost) : Prop where
  rows_length : newRows.length = cost.length
  columns_length : newColumns.length = cost.length
  rows_exact : chosen cost (alloc.vec.Vec.deref newRows) = Assignment.searchRows assignment root (chosen cost (alloc.vec.Vec.deref newColumns))
  free_outside : assignment root ∉ chosen cost (alloc.vec.Vec.deref newColumns)
  steps_card : next.val = (chosen cost (alloc.vec.Vec.deref newColumns)).card + if searching then 0 else 1
  discovered_exact : discovered cost newColumns assignment root searching = insert column (chosen cost (alloc.vec.Vec.deref oldColumns))
  rows_mono : chosen cost (alloc.vec.Vec.deref oldRows) ⊆ chosen cost (alloc.vec.Vec.deref newRows)

/-- Both real branches of the Rust write frame preserve the alternating-cut
shape, free target and exact visit count. The newly recorded predecessor
column is added to the discovered set even on the terminal branch. -/
theorem step_cut_frame (cost : Slice (alloc.vec.Vec (Option I64))) (n : Usize)
    (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost) (inverse : alloc.vec.Vec Usize) (target : Usize)
    (initialRows initialColumns : Vertex cost → ℤ) (increment : ℤ)
    (rows columns : alloc.vec.Vec I128) (selectedRows selectedColumns : alloc.vec.Vec Bool)
    (predecessor discovery : alloc.vec.Vec Usize) (steps : Usize) (searching : Bool) (failure : Option AssignmentError)
    (input : Input cost n assignment root inverse target initialRows initialColumns)
    (h : Invariant cost assignment root initialRows initialColumns increment rows columns selectedRows selectedColumns predecessor discovery steps searching failure)
    (hs : searching = true) (step : sparse.SparseStep) (next : Usize) (hNext : next.val = steps.val+1)
    (hp : StepProgress cost (alloc.vec.Vec.deref rows) (alloc.vec.Vec.deref columns)
      (alloc.vec.Vec.deref selectedRows) (alloc.vec.Vec.deref selectedColumns) initialRows initialColumns increment step) :
    ∃ hc : step.cut.column.val < cost.length,
      CutFrame cost assignment root selectedRows selectedColumns
        (if step.cut.column = target then selectedRows else selectedRows.set inverse.val[step.cut.column.val]! true)
        (if step.cut.column = target then selectedColumns else selectedColumns.set step.cut.column true)
        next (decide (step.cut.column ≠ target)) ⟨step.cut.column.val,hc⟩ := by
  obtain ⟨row,column,hRow,hColumn,hSelected,hUnselected,hAllowed,hDelta,hTight⟩ := hp.tight_edge
  have hc : step.cut.column.val < cost.length := by rw [← hColumn]; exact column.isLt
  refine ⟨hc,?_⟩
  have hCol : (⟨step.cut.column.val,hc⟩ : Vertex cost) = column := Fin.ext hColumn.symm
  have hSteps : steps.val = (chosen cost (alloc.vec.Vec.deref selectedColumns)).card := by
    simpa only [hs,↓reduceIte,Nat.add_zero] using h.steps_card
  by_cases ht : step.cut.column = target
  · have he : column = assignment root := by
      apply Fin.ext
      rw [hColumn,ht,input.target_eq]
    simp only [ht,↓reduceIte,ne_eq,not_true_eq_false,decide_false]
    refine ⟨h.selected_rows_length,h.selected_columns_length,h.rows_exact,h.free_outside,?_,?_,Finset.Subset.refl _⟩
    · simp only [Bool.false_eq_true,↓reduceIte]
      omega
    · have hh : discovered cost selectedColumns assignment root false =
          insert (⟨step.cut.column.val,hc⟩ : Vertex cost) (chosen cost (alloc.vec.Vec.deref selectedColumns)) := by
        rw [hCol,he]
        simp [discovered,Finset.union_comm]
      simpa only [ht] using hh
  · have hNewRow : inverse.val[step.cut.column.val]!.val = (assignment.symm column).val := by
      simpa only [hCol] using input.inverse_values ⟨step.cut.column.val,hc⟩
    have hr : inverse.val[step.cut.column.val]!.val < cost.length := by rw [hNewRow]; exact (assignment.symm column).isLt
    have hn : column ≠ assignment root := by
      intro he
      apply ht
      apply UScalar.eq_of_val_eq
      rw [← hColumn,he,input.target_eq]
    have hCols := chosen_set_true cost selectedColumns step.cut.column h.selected_columns_length hc
    have hRows := chosen_set_true cost selectedRows inverse.val[step.cut.column.val]! h.selected_rows_length hr
    simp only [ht,↓reduceIte,ne_eq,not_false_eq_true,decide_true]
    refine ⟨by simpa using h.selected_rows_length,by simpa using h.selected_columns_length,?_,?_,?_,?_,?_⟩
    · exact chosen_search_extension cost selectedRows selectedColumns assignment root step.cut.column inverse.val[step.cut.column.val]!
        h.selected_columns_length h.selected_rows_length hc hr (by rw [hCol]; exact hNewRow) h.rows_exact
    · rw [hCols,hCol]
      simp only [Finset.mem_insert,not_or]
      exact ⟨Ne.symm hn,h.free_outside⟩
    · rw [hCols,hCol,Finset.card_insert_of_notMem hUnselected]
      simp only [↓reduceIte,Nat.add_zero]
      omega
    · simp only [discovered,↓reduceIte,Finset.union_empty]
      exact hCols
    · rw [hRows]
      exact Finset.subset_insert _ _

end SubtreeProofs.Rust.SparseSearch

end
