module

public import SubtreeProofs.Rust.AssignmentDriverAugmentation
import Mathlib.Tactic

/-!
# Actual outer assignment-driver body

The real reserved-pointer write, complete search and actual augmentation add
exactly the current row, preserving full numeric and tightness invariants.
The actual row increment is safe and provides the outer termination measure.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentDriverBody

open AssignmentColumnScan AssignmentScanInvariant AssignmentSearchInitialization AssignmentSearchLoop
open AssignmentAugmentationMatching AssignmentDriverInvariant AssignmentDriverAugmentation

/-- Complete actual running driver iteration, including search and
augmentation, safely increases independent covered-row count by one. -/
theorem body_running_spec (cost : Slice (alloc.vec.Vec I64)) (n extent : Usize) (input : Input cost n extent)
    (u v : alloc.vec.Vec I128) (matched predecessor : alloc.vec.Vec Usize) (row : Usize)
    (h : Invariant cost n u v matched predecessor row none) (hr : row.val ≤ n.val) :
    finish_assignment_loop.body cost n extent u v matched predecessor row none ⦃ output =>
      ∃ next : DriverState, output = .cont next ∧ StateInvariant cost n next ∧ next.2.2.2.2.1.val = row.val+1 ⦄ := by
  have hrow : row ≤ n := hr
  have hn := input.n_max cost n extent
  have hzero : (0#usize).val < matched.length := by have hb := h.matched_len; scalar_tac
  have hsearchInput := search_input cost n extent input u v matched predecessor row h hr
  have hmatching : Assignment.PartialRows n.val (row.val-1) (pointers (matched.set 0#usize row)) := by
    change Assignment.PartialRows n.val (row.val-1) (fun col => (matched.set 0#usize row).val[col]!.val)
    simpa only [alloc.vec.Vec.deref,Slice.from_val] using hsearchInput.matching
  have hroot : pointers (matched.set 0#usize row) 0 = row.val-1+1 := by
    simpa only [pointers,alloc.vec.Vec.deref,Slice.from_val] using hsearchInput.root
  have htight := set_root_tight cost u v matched n row h.matched_len h.matching_tight
  unfold finish_assignment_loop.body
  simp only [hrow,↓reduceIte,core.option.Option.is_none,alloc.vec.Vec.index_mut_slice_index]
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec matched 0#usize hzero)
  rintro ⟨_,back⟩ ⟨_,hback⟩
  simp only [uncurry_apply_pair,hback]
  apply WP.spec_bind (find_augmenting_column_spec cost (alloc.vec.Vec.deref (matched.set 0#usize row)) n extent (row.val-1)
    (initialRows cost n) hsearchInput u v predecessor h.u_len h.v_len h.predecessor_len h.potential htight)
  rintro ⟨searchResult,newU,newV,newPred⟩ ⟨column,hSearchResult,hfound⟩
  dsimp only at hSearchResult hfound ⊢
  subst searchResult
  simp only [uncurry_apply_pair,Std.bind_assoc]
  apply WP.spec_bind (augment_found_spec cost n (row.val-1) (initialRows cost n) newU newV (matched.set 0#usize row) newPred column
    (by simpa using h.matched_len) hmatching hroot hfound)
  rintro ⟨augmentResult,newMatched⟩ ⟨hAugmentResult,hmatchedLen,hpartial,hnewTight⟩
  dsimp only at hAugmentResult hmatchedLen hpartial hnewTight ⊢
  subst augmentResult
  simp only [uncurry_apply_pair,bind_ok]
  apply WP.spec_bind (Usize.add_spec (x := row) (y := 1#usize) (by scalar_tac))
  intro nextRow hNextRow
  have hnext : nextRow.val = row.val+1 := by simpa using hNextRow
  simp only [WP.spec_ok]
  refine ⟨_,rfl,?_,hnext⟩
  change Invariant cost n newU newV newMatched newPred nextRow none
  refine {
    u_len := hfound.u_len, v_len := hfound.v_len, matched_len := ?_, predecessor_len := hfound.predecessor_len,
    row_positive := by omega, row_bound := by omega, failure_none := rfl,
    matching := ?_, potential := hfound.potential, matching_tight := hnewTight }
  · rw [hmatchedLen]
    simpa using h.matched_len
  · have he : row.val-1+1 = nextRow.val-1 := by have hp := h.row_positive; omega
    simpa only [he] using hpartial

/-- The actual stopped driver branch returns current data without another
search, index operation or arithmetic update. -/
theorem body_done_spec (cost : Slice (alloc.vec.Vec I64)) (n extent : Usize)
    (u v : alloc.vec.Vec I128) (matched predecessor : alloc.vec.Vec Usize) (row : Usize)
    (hr : n.val < row.val) :
    finish_assignment_loop.body cost n extent u v matched predecessor row none ⦃ output =>
      output = .done (u,v,matched,none) ⦄ := by
  have hnot : ¬ row ≤ n := by scalar_tac
  simp [finish_assignment_loop.body,hnot]

end SubtreeProofs.Rust.AssignmentDriverBody

end
