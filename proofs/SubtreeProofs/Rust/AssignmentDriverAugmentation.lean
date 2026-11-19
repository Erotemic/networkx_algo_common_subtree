module

public import SubtreeProofs.Rust.AssignmentDriverInvariant
import Mathlib.Tactic

/-!
# Actual driver augmentation from the actual search result

The verified search constructs the ranked tight predecessor forest consumed
by verified augmentation. This bridge preserves the physical matching-vector
length and extends independent row coverage and tightness by one fresh row.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentDriverAugmentation

open AssignmentAugmentationMatching AssignmentPredecessorTightness AssignmentSearchLoop

/-- The actual augmentation consumes exactly the structural result produced
by actual search, adding one row while preserving matching tightness. -/
theorem augment_found_spec (cost : Slice (alloc.vec.Vec I64)) (n : Usize) (filled : Nat) (initialRows : Fin n.val → ℤ)
    (u v : alloc.vec.Vec I128) (matched predecessor : alloc.vec.Vec Usize) (column : Usize)
    (hmatched : n.val < matched.length) (hpartial : Assignment.PartialRows n.val filled (pointers matched))
    (hroot : pointers matched 0 = filled+1)
    (hfound : Found cost (alloc.vec.Vec.deref matched) n initialRows u v predecessor column) :
    augment_matching matched (alloc.vec.Vec.deref predecessor) column n ⦃ output =>
      output.1 = core.result.Result.Ok () ∧ output.2.length = matched.length ∧
        Assignment.PartialRows n.val (filled+1) (pointers output.2) ∧
          Assignment.TightPointers n.val (AssignmentReconstruction.pointerMatrix cost)
            (fun row => u.val[row]!.val) (fun col => v.val[col]!.val) (pointers output.2) ⦄ := by
  obtain ⟨vertices,rank,hcol,hranked,hforest⟩ := hfound.forest
  have htight : Assignment.TightPointers n.val (AssignmentReconstruction.pointerMatrix cost)
      (fun row => u.val[row]!.val) (fun col => v.val[col]!.val) (pointers matched) := by
    simpa only [Assignment.TightPointers,pointers,alloc.vec.Vec.deref,Slice.from_val] using hfound.matching_tight
  have hfree : pointers matched column.val = 0 := by
    simpa only [pointers,alloc.vec.Vec.deref,Slice.from_val] using hfound.free
  apply WP.spec_mono (augment_matching_ranked_tight_spec matched (alloc.vec.Vec.deref predecessor) column n filled vertices rank
    hranked hcol hfound.column_positive hmatched (by simpa only [alloc.vec.Vec.deref,Slice.length,Slice.from_val,alloc.vec.Vec.length] using hfound.predecessor_len) hpartial hroot hfree
    (AssignmentReconstruction.pointerMatrix cost) (fun row => u.val[row]!.val) (fun col => v.val[col]!.val) htight (by
      intro col hc hz
      simpa only [ForestTight,pointers,alloc.vec.Vec.deref,Slice.from_val] using hforest col hc hz))
  rintro output ⟨hsuccess,hpartial,htight,hlen⟩
  exact ⟨hsuccess,hlen,hpartial,htight⟩

end SubtreeProofs.Rust.AssignmentDriverAugmentation

end
