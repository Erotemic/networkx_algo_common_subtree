module

public import SubtreeProofs.Rust.SparseSearchBody
import Mathlib.Tactic

/-! # Actual sparse cut updates retain old matching and predecessor tightness -/

@[expose] public section

open Aeneas Aeneas.Std
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseSearch

open SparseCut

/-- Both endpoints of an old selected predecessor edge lie in the cut, so
its exact tightness persists in the physical vectors returned by Rust. -/
theorem step_selected_edge_tight (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : alloc.vec.Vec I128)
    (selectedRows selectedColumns : alloc.vec.Vec Bool) (initialRows initialColumns : Vertex cost → ℤ)
    (increment : ℤ) (step : sparse.SparseStep)
    (h : StepProgress cost (alloc.vec.Vec.deref rows) (alloc.vec.Vec.deref columns)
      (alloc.vec.Vec.deref selectedRows) (alloc.vec.Vec.deref selectedColumns) initialRows initialColumns increment step)
    (row column : Vertex cost) (hr : row ∈ chosen cost (alloc.vec.Vec.deref selectedRows))
    (hc : column ∈ chosen cost (alloc.vec.Vec.deref selectedColumns))
    (ht : potentialAt cost (alloc.vec.Vec.deref rows) row+potentialAt cost (alloc.vec.Vec.deref columns) column = matrix cost row column) :
    potentialAt cost (alloc.vec.Vec.deref step.rows) row+potentialAt cost (alloc.vec.Vec.deref step.columns) column = matrix cost row column := by
  rw [h.rows_exact,h.columns_exact]
  exact Assignment.adjust_preserves_tight_edge (matrix cost) _ _ _ _ step.cut.delta.val row column ht (iff_of_true hr hc)

theorem step_matching_tight (cost : Slice (alloc.vec.Vec (Option I64))) (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost)
    (initialRows initialColumns : Vertex cost → ℤ) (increment : ℤ)
    (rows columns : alloc.vec.Vec I128) (selectedRows selectedColumns : alloc.vec.Vec Bool)
    (predecessor discovery : alloc.vec.Vec Usize) (steps : Usize) (searching : Bool) (failure : Option AssignmentError)
    (h : Invariant cost assignment root initialRows initialColumns increment rows columns selectedRows selectedColumns predecessor discovery steps searching failure)
    (step : sparse.SparseStep)
    (hp : StepProgress cost (alloc.vec.Vec.deref rows) (alloc.vec.Vec.deref columns)
      (alloc.vec.Vec.deref selectedRows) (alloc.vec.Vec.deref selectedColumns) initialRows initialColumns increment step) :
    ∀ row, row ≠ root → potentialAt cost (alloc.vec.Vec.deref step.rows) row+
      potentialAt cost (alloc.vec.Vec.deref step.columns) (assignment row) = matrix cost row (assignment row) := by
  rw [hp.rows_exact,hp.columns_exact,h.rows_exact]
  exact Assignment.search_adjust_preserves_matching assignment root _ (matrix cost) _ _ step.cut.delta.val h.matching_tight

/-- Every old discovered predecessor remains a selected allowed tight edge
after an actual active cut update. The rank relationships here still refer
to the old arrays; the separate write frame updates the new column. -/
theorem step_old_predecessors (cost : Slice (alloc.vec.Vec (Option I64))) (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost)
    (initialRows initialColumns : Vertex cost → ℤ) (increment : ℤ)
    (rows columns : alloc.vec.Vec I128) (selectedRows selectedColumns : alloc.vec.Vec Bool)
    (predecessor discovery : alloc.vec.Vec Usize) (steps : Usize) (searching : Bool) (failure : Option AssignmentError)
    (h : Invariant cost assignment root initialRows initialColumns increment rows columns selectedRows selectedColumns predecessor discovery steps searching failure)
    (hs : searching = true) (step : sparse.SparseStep)
    (hp : StepProgress cost (alloc.vec.Vec.deref rows) (alloc.vec.Vec.deref columns)
      (alloc.vec.Vec.deref selectedRows) (alloc.vec.Vec.deref selectedColumns) initialRows initialColumns increment step) :
    ∀ column ∈ chosen cost (alloc.vec.Vec.deref selectedColumns), ∃ row : Vertex cost,
      predecessor.val[column.val]!.val = row.val ∧ row ∈ chosen cost (alloc.vec.Vec.deref selectedRows) ∧ allowed cost row column ∧
      potentialAt cost (alloc.vec.Vec.deref step.rows) row+potentialAt cost (alloc.vec.Vec.deref step.columns) column = matrix cost row column ∧
      (row = root ∨ 0 < discovery.val[(assignment row).val]!.val ∧
        discovery.val[(assignment row).val]!.val < discovery.val[column.val]!.val) := by
  intro column hc
  have hd : column ∈ discovered cost selectedColumns assignment root searching := by
    simpa only [discovered,hs,↓reduceIte,Finset.union_empty] using hc
  obtain ⟨row,hPred,hRow,hAllowed,hTight,hRank⟩ := h.predecessor_edges column hd
  exact ⟨row,hPred,hRow,hAllowed,
    step_selected_edge_tight cost rows columns selectedRows selectedColumns initialRows initialColumns increment step hp row column hRow hc hTight,hRank⟩

end SubtreeProofs.Rust.SparseSearch

end
