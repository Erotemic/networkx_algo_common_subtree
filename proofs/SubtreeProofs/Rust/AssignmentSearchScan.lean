module

public import SubtreeProofs.Rust.AssignmentSearchInvariant
import Mathlib.Tactic

/-!
# Actual column scan from the combined search invariant

The real scan's representation and arithmetic premises are derived from the
combined invariant. Its successful result carries nonnegative attained cut
bounds, exact table frames and a physical predecessor in the visited set.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentSearchScan

open AssignmentColumnScan AssignmentScanInvariant AssignmentScanCut AssignmentAdjustmentInvariant AssignmentSearchCapacity
open AssignmentNumericBounds AssignmentSearchArithmetic AssignmentSearchInvariant AssignmentVisitColumn AssignmentCutFeasibility

structure Scanned (cost : Slice (alloc.vec.Vec I64)) (u v : alloc.vec.Vec I128) (matched : Slice Usize)
    (used : alloc.vec.Vec Bool) (slack : alloc.vec.Vec (Option I128)) (predecessor : alloc.vec.Vec Usize)
    (column n : Usize) (amount : I128) (selected : Usize)
    (newSlack : alloc.vec.Vec (Option I128)) (newPred : alloc.vec.Vec Usize) : Prop where
  selected_positive : 0 < selected.val
  selected_bound : selected.val ≤ n.val
  selected_free : used.val[selected.val]! = false
  nonnegative : 0 ≤ amount.val
  physical : newSlack.val[selected.val]! = some amount
  slacks : SlackInvariant cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) matched (alloc.vec.Vec.deref used)
    (usedIndices (alloc.vec.Vec.deref used) (n.val+1)) newSlack newPred n
  predecessor_member : newPred.val[selected.val]!.val ∈ usedIndices (alloc.vec.Vec.deref used) (n.val+1)
  attained : amount.val = candidateCost cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) matched selected.val newPred.val[selected.val]!.val
  slack_frame : SlackPrefix (alloc.vec.Vec.deref used) (columnWeight cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) slack matched.val[column.val]!)
    slack newSlack (n.val+1)
  predecessor_frame : PredecessorPrefix (alloc.vec.Vec.deref used) (columnWeight cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) slack matched.val[column.val]!)
    slack predecessor newPred column (n.val+1)
  minimum : ∀ target, 0 < target → target ≤ n.val → used.val[target]! = false →
    ∀ candidate ∈ usedIndices (alloc.vec.Vec.deref used) (n.val+1), amount.val ≤
      candidateCost cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) matched target candidate

/-- The complete actual source scan succeeds directly from the combined
invariant after marking the current column. Local machine ranges, an
available column, nonnegative adjustment and an attaining predecessor are
all derived, rather than supplied as arithmetic or result certificates. -/
theorem scan_from_invariant_spec (cost : Slice (alloc.vec.Vec I64)) (matched : Slice Usize) (n extent : Usize)
    (filled : Nat) (initialRows : Fin n.val → ℤ) (input : Input cost matched n extent filled initialRows)
    (u v : alloc.vec.Vec I128) (predecessor : alloc.vec.Vec Usize) (column : Usize)
    (slack : alloc.vec.Vec (Option I128)) (used : alloc.vec.Vec Bool) (visited : Usize) (searching : Bool)
    (failure : Option AssignmentError)
    (h : Invariant cost matched n initialRows u v predecessor column slack used visited searching failure)
    (hsearching : searching = true) :
    scan_columns cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) (alloc.vec.Vec.deref (used.set column true))
      slack predecessor column matched.val[column.val]! n ⦃ output =>
        ∃ amount : I128, ∃ selected : Usize, output.1 = core.result.Result.Ok (amount,selected) ∧
          Scanned cost u v matched (used.set column true) slack predecessor column n amount selected output.2.1 output.2.2 ⦄ := by
  have bounds := h.scan_bounds_after_mark cost matched n extent filled initialRows input u v predecessor column slack used visited searching failure hsearching
  have hcurrent := h.searching_exact.mp hsearching
  have hmarked := mark_matched matched used n column h.used_len h.column_bound h.used_matched hcurrent
  have havailable := unused_free_column matched (alloc.vec.Vec.deref (used.set column true)) n filled input.matching input.filled_lt hmarked
  have hslack := mark_slackInvariant cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) matched used
    (usedIndices (alloc.vec.Vec.deref used) (n.val+1)) slack predecessor n column h.used_len h.column_bound h.slacks
  have hfits : ∀ candidate : Usize, 0 < candidate.val → candidate.val ≤ n.val →
      (alloc.vec.Vec.deref (used.set column true)).val[candidate.val]! = false →
        Fits128 (firstReduced cost (alloc.vec.Vec.deref u) matched.val[column.val]! candidate) ∧
        Fits128 (reducedCost cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) matched.val[column.val]! candidate) := by
    intro candidate hp hb _
    exact scan_subtractions_fit cost u v n matched.val[column.val]! candidate initialRows (-v.val[0]!.val)
      input.n_size bounds.row_pos bounds.row_le hp hb h.potential.envelope input.initial_bounds
      (h.potential.increment_bound cost n initialRows u v input.initial_bounds) h.potential.feasible
  apply WP.spec_mono (scan_columns_cut_spec cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) matched
    (alloc.vec.Vec.deref (used.set column true)) (usedIndices (alloc.vec.Vec.deref used) (n.val+1)) slack predecessor column n bounds hfits
    (by obtain ⟨col,hp,hb,hf,_⟩ := havailable; exact ⟨col,hp,hb,hf⟩) hslack)
  rintro output ⟨amount,selected,houtput,hp,hb,hf,hphysical,hnewSlack,hmember,hattained,hslackFrame,hpredFrame,hminimum⟩
  have hset := (usedIndices_set_true used n column h.column_bound h.used_len).symm
  rw [hset] at hnewSlack hmember hminimum
  have hc := (mem_usedIndices (alloc.vec.Vec.deref (used.set column true)) _ _).mp hmember
  have hcandidate : output.2.2.val[selected.val]!.val ≤ n.val := by omega
  have hnonzero := hmarked _ hcandidate hc.2
  have hr := nonzero_pointer_bounds matched n filled _ input.matching input.root input.filled_lt hcandidate hnonzero
  have hnonnegative := attained_nonnegative cost u v matched n amount selected.val output.2.2.val[selected.val]!.val hp hb hr.1 hr.2 h.potential.feasible hattained
  refine ⟨amount,selected,houtput,?_,?_,?_,hnonnegative,hphysical,hnewSlack,hmember,hattained,hslackFrame,hpredFrame,?_⟩
  · exact hp
  · exact hb
  · simpa only [alloc.vec.Vec.deref,Slice.from_val] using hf
  · intro target htp htb htf candidate hcm
    exact hminimum target htp htb (by simpa only [alloc.vec.Vec.deref,Slice.from_val] using htf) candidate hcm

end SubtreeProofs.Rust.AssignmentSearchScan

end
