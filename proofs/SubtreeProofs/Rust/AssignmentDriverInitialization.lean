module

public import SubtreeProofs.Rust.AssignmentDriverInvariant
import Mathlib.Tactic

/-!
# Initial outer driver invariant from actual initializer contents

The actual row-minimum vector and three zero-fill vectors establish zero
covered rows, feasible numeric accounting and vacuous matching tightness.
Reserved pointer zero will be populated by each actual driver iteration.
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace SubtreeProofs.Rust.AssignmentDriverInitialization

open AssignmentPotentialInitialization AssignmentSearchInitialization AssignmentAugmentationMatching AssignmentDriverInvariant

/-- Exact actual initializer contents establish every independent driver
invariant, including empty input and zero matched rows. -/
theorem initial_invariant (cost : Slice (alloc.vec.Vec I64)) (n extent : Usize) (input : Input cost n extent)
    (u v : alloc.vec.Vec I128) (matched predecessor : alloc.vec.Vec Usize)
    (hinit : Initialized cost u cost.length) (hv : v.val = List.replicate extent.val 0#i128)
    (hm : matched.val = List.replicate extent.val 0#usize) (hp : predecessor.val = List.replicate extent.val 0#usize) :
    Invariant cost n u v matched predecessor 1#usize none := by
  have hvalue : ∀ col, col ≤ n.val → pointers matched col = 0 := by
    intro col hb
    have hi : col < extent.val := by rw [input.extent_eq]; omega
    unfold pointers
    rw [hm,getElem!_pos (List.replicate extent.val 0#usize) col (by simpa only [List.length_replicate] using hi)]
    simp
  have hmatching : Assignment.PartialRows n.val 0 (pointers matched) := by
    apply (Assignment.partialRows_zero n.val).congr
    intro col _ hb
    exact (hvalue col hb).symm
  refine {
    u_len := ?_, v_len := ?_, matched_len := ?_, predecessor_len := ?_,
    row_positive := by simp, row_bound := by simp, failure_none := rfl,
    matching := by simpa using hmatching, potential := ?_, matching_tight := ?_ }
  · rw [hinit.1,input.cost_len]
    omega
  · change n.val < v.val.length
    rw [hv,List.length_replicate,input.extent_eq]
    omega
  · change n.val < matched.val.length
    rw [hm,List.length_replicate,input.extent_eq]
    omega
  · change n.val < predecessor.val.length
    rw [hp,List.length_replicate,input.extent_eq]
    omega
  · exact initial_potentialInvariant cost u v n input.cost_len input.square hinit (by simpa only [input.extent_eq] using hv)
  · intro col _ hb hn
    have hh := hvalue col hb
    change pointers matched col ≠ 0 at hn
    exact False.elim (hn hh)

end SubtreeProofs.Rust.AssignmentDriverInitialization

end
