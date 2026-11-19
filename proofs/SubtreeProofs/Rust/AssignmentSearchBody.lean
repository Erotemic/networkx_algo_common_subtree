module

public import SubtreeProofs.Rust.AssignmentSearchTransition
import Mathlib.Tactic

/-!
# Actual alternating-tree search body

The complete generated running branch is verified: visit checks, boolean
mark, active-row checks, actual scan, actual checked adjustment and next
pointer read. Successful execution preserves the combined invariant and
increments the actual visit count. The stopped branch returns unchanged.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentSearchBody

open AssignmentColumnScan AssignmentScanInvariant AssignmentNumericBounds AssignmentSearchInvariant AssignmentSearchScan
open AssignmentSearchAdjustment AssignmentSearchTransition AssignmentVisitColumn

def visitCount (state : SearchState) : Nat := state.2.2.2.2.2.2.1.val

/-- The entire actual running source body succeeds and advances to another
valid combined state. No arithmetic, indexing or invariant-error branch is
assumed successful; each is discharged from the independent input/state. -/
theorem body_running_spec (cost : Slice (alloc.vec.Vec I64)) (matched : Slice Usize) (n extent : Usize)
    (filled : Nat) (initialRows : Fin n.val → ℤ) (input : Input cost matched n extent filled initialRows)
    (u v : alloc.vec.Vec I128) (predecessor : alloc.vec.Vec Usize) (column : Usize)
    (slack : alloc.vec.Vec (Option I128)) (used : alloc.vec.Vec Bool) (visited : Usize)
    (h : Invariant cost matched n initialRows u v predecessor column slack used visited true none) :
    find_augmenting_column_loop.body cost matched n u v predecessor column slack used visited true none ⦃ output =>
      ∃ next : SearchState, output = .cont next ∧ StateInvariant cost matched n initialRows next ∧
        visitCount next = visited.val+1 ⦄ := by
  have hv := h.visit_guard cost matched n extent filled initialRows input u v predecessor column slack used visited true none rfl
  have hrow := nonzero_pointer_bounds matched n filled column.val input.matching input.root input.filled_lt h.column_bound (h.searching_exact.mp rfl)
  have hcolumn : column.val < used.length := lt_of_le_of_lt h.column_bound h.used_len
  have hmatched : column.val < matched.length := lt_of_le_of_lt h.column_bound input.matched_len
  have hnotVisit : ¬ visited >= n := by scalar_tac
  unfold find_augmenting_column_loop.body
  simp only [core.option.Option.is_none,hnotVisit,↓reduceIte,Std.bind_assoc,alloc.vec.Vec.index_slice_index]
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec used column hcolumn)
  intro flag hFlag
  have hflag : flag = false := by
    rw [hFlag]
    simpa only [getElem!_pos used.val column.val hcolumn] using h.column_free
  simp only [hflag,Bool.false_eq_true,↓reduceIte,bind_ok]
  apply WP.spec_bind (Usize.add_spec (x := visited) (y := 1#usize) (by scalar_tac))
  intro nextVisited hNextVisited
  have hnext : nextVisited.val = visited.val+1 := by simpa using hNextVisited
  simp only [alloc.vec.Vec.index_mut_slice_index]
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec used column hcolumn)
  rintro ⟨_,back⟩ ⟨_,hback⟩
  simp only [uncurry_apply_pair]
  apply WP.spec_bind (Slice.index_usize_spec matched column hmatched)
  intro activeRow hActiveRow
  have hactive : activeRow = matched.val[column.val]! := by
    simpa only [getElem!_pos matched.val column.val hmatched] using hActiveRow
  have ha0 : matched.val[column.val]! ≠ 0#usize := by scalar_tac
  have hab : ¬ matched.val[column.val]! > n := by scalar_tac
  simp only [hactive,ha0,hab,↓reduceIte,hback,bind_ok,uncurry_apply_pair]
  apply WP.spec_bind (scan_from_invariant_spec cost matched n extent filled initialRows input u v predecessor column slack used visited true none h rfl)
  rintro ⟨scanResult,newSlack,newPred⟩ ⟨amount,selected,hScanResult,hscan⟩
  dsimp only at hScanResult hscan ⊢
  subst scanResult
  simp only [uncurry_apply_pair]
  apply WP.spec_bind (adjustment_from_scan_spec cost matched n extent filled initialRows input u v predecessor column slack used visited true none h rfl
    amount selected newSlack newPred hscan)
  rintro ⟨adjustResult,newU,newV,finalSlack⟩ hadjust
  have hr := hadjust.complete.1
  change adjustResult = core.result.Result.Ok () at hr
  subst adjustResult
  simp only [uncurry_apply_pair]
  have hselected : selected.val < matched.length := lt_of_le_of_lt hscan.selected_bound input.matched_len
  apply WP.spec_bind (Slice.index_usize_spec matched selected hselected)
  intro assigned hAssigned
  have hassigned : assigned = matched.val[selected.val]! := by
    simpa only [getElem!_pos matched.val selected.val hselected] using hAssigned
  simp only [hassigned,WP.spec_ok]
  refine ⟨_,rfl,?_,hnext⟩
  exact next_invariant cost matched n initialRows u v predecessor column slack used visited h amount selected newSlack newPred hscan
    newU newV finalSlack hadjust nextVisited hnext

/-- The stopped source branch performs no further read or update. -/
theorem body_done_spec (cost : Slice (alloc.vec.Vec I64)) (matched : Slice Usize) (n : Usize)
    (u v : alloc.vec.Vec I128) (predecessor : alloc.vec.Vec Usize) (column : Usize)
    (slack : alloc.vec.Vec (Option I128)) (used : alloc.vec.Vec Bool) (visited : Usize) :
    find_augmenting_column_loop.body cost matched n u v predecessor column slack used visited false none ⦃ output =>
      output = .done (u,v,predecessor,column,none) ⦄ := by
  simp [find_augmenting_column_loop.body]

end SubtreeProofs.Rust.AssignmentSearchBody

end
