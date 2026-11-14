module

public import SubtreeProofs.Rust.SparseSearchInvariant
import Mathlib.Tactic

/-! # Exact checked writes of one actual sparse alternating-search iteration -/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseSearch

open SparseCut AssignmentNumericBounds

def afterStep (inverse : alloc.vec.Vec Usize) (target : Usize)
    (selectedRows selectedColumns : alloc.vec.Vec Bool) (predecessor discovery : alloc.vec.Vec Usize)
    (step : sparse.SparseStep) (next : Usize) : SearchState :=
  (step.rows,step.columns,
    if step.cut.column = target then selectedRows else selectedRows.set inverse.val[step.cut.column.val]! true,
    if step.cut.column = target then selectedColumns else selectedColumns.set step.cut.column true,
    predecessor.set step.cut.column step.cut.row,discovery.set step.cut.column next,next,decide (step.cut.column ≠ target),none)

/-- Every actual active iteration executes a safe attained cut step and
records its exact original-index predecessor, discovery rank and flag writes.
All source error branches and bounds are discharged by the independent state;
preservation of the whole invariant is proved separately from this write frame. -/
theorem body_step_spec (cost : Slice (alloc.vec.Vec (Option I64))) (n : Usize)
    (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost) (inverse : alloc.vec.Vec Usize) (target : Usize)
    (initialRows initialColumns : Vertex cost → ℤ) (increment : ℤ)
    (rows columns : alloc.vec.Vec I128) (selectedRows selectedColumns : alloc.vec.Vec Bool)
    (predecessor discovery : alloc.vec.Vec Usize) (steps : Usize) (searching : Bool) (failure : Option AssignmentError)
    (input : Input cost n assignment root inverse target initialRows initialColumns)
    (h : Invariant cost assignment root initialRows initialColumns increment rows columns selectedRows selectedColumns predecessor discovery steps searching failure)
    (hs : searching = true) :
    sparse_search.find_sparse_augmenting_path_loop.body cost n inverse target rows columns selectedRows selectedColumns predecessor discovery steps searching failure ⦃ result =>
      ∃ step next, StepProgress cost (alloc.vec.Vec.deref rows) (alloc.vec.Vec.deref columns)
        (alloc.vec.Vec.deref selectedRows) (alloc.vec.Vec.deref selectedColumns) initialRows initialColumns increment step ∧
        next.val = steps.val+1 ∧ result = .cont (afterStep inverse target selectedRows selectedColumns predecessor discovery step next) ⦄ := by
  have hVisit := h.visit_guard cost n assignment root initialRows initialColumns increment rows columns selectedRows selectedColumns predecessor discovery steps searching failure input.n_eq hs
  have hGuard : ¬ steps ≥ n := by scalar_tac
  unfold sparse_search.find_sparse_augmenting_path_loop.body
  simp only [hs,h.failure_none,hGuard,↓reduceIte,core.option.Option.is_none,bind_ok]
  apply WP.spec_bind (Usize.add_spec (x := steps) (y := 1#usize) (by scalar_tac))
  intro next hNext
  apply WP.spec_bind (h.advance_spec cost n assignment root inverse target initialRows initialColumns increment
    rows columns selectedRows selectedColumns predecessor discovery steps searching failure input)
  rintro result ⟨step,rfl,hProgress⟩
  obtain ⟨row,column,hRow,hColumn,hSelected,hUnselected,hAllowed,hDelta,hTight⟩ := hProgress.tight_edge
  have hc : step.cut.column.val < cost.length := by rw [← hColumn]; exact column.isLt
  simp only [alloc.vec.Vec.index_mut_slice_index]
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec predecessor step.cut.column (by rw [h.predecessor_length]; exact hc))
  rintro ⟨_,predBack⟩ ⟨_,hPred⟩
  simp only [uncurry_apply_pair]
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec discovery step.cut.column (by rw [h.discovery_length]; exact hc))
  rintro ⟨_,rankBack⟩ ⟨_,hRank⟩
  simp only [uncurry_apply_pair]
  by_cases ht : step.cut.column = target
  · simp only [ht,↓reduceIte]
    apply (WP.spec_ok _).mpr
    refine ⟨step,next,hProgress,by simpa only [UScalar.ofNatCore_val_eq] using hNext,?_⟩
    simp only [afterStep,ht,↓reduceIte,ne_eq,not_true_eq_false,decide_false,hPred,hRank]
  · simp only [ht,↓reduceIte]
    apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec selectedColumns step.cut.column (by rw [h.selected_columns_length]; exact hc))
    rintro ⟨_,columnBack⟩ ⟨_,hColumnBack⟩
    simp only [uncurry_apply_pair,alloc.vec.Vec.index_slice_index]
    apply WP.spec_bind (alloc.vec.Vec.index_usize_spec inverse step.cut.column (by rw [input.inverse_length]; exact hc))
    intro matched hMatched
    have hm : matched = inverse.val[step.cut.column.val]! := by
      simpa only [getElem!_pos inverse.val step.cut.column.val (by change step.cut.column.val < inverse.length; rw [input.inverse_length]; exact hc)] using hMatched
    have hb : matched.val < cost.length := by
      have hi := input.inverse_values ⟨step.cut.column.val,hc⟩
      rw [hm,hi]
      exact (assignment.symm ⟨step.cut.column.val,hc⟩).isLt
    apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec selectedRows matched (by rw [h.selected_rows_length]; exact hb))
    rintro ⟨_,rowBack⟩ ⟨_,hRowBack⟩
    apply (WP.spec_ok _).mpr
    refine ⟨step,next,hProgress,by simpa only [UScalar.ofNatCore_val_eq] using hNext,?_⟩
    simp only [afterStep,ht,↓reduceIte,ne_eq,not_false_eq_true,decide_true,hPred,hRank,hColumnBack,hRowBack,hm,hs]

end SubtreeProofs.Rust.SparseSearch

end
