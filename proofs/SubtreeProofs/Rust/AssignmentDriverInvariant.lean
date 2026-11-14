module

public import SubtreeProofs.Rust.AssignmentSearchLoop
import Mathlib.Tactic

/-!
# Independent row-coverage invariant for the actual assignment driver

The driver covers precisely the rows before its current row counter. Writing
the fresh row into reserved pointer zero preserves every real pointer and
establishes the verified search's independent input. Discovery and numeric
certificates are constructed by the search, rather than supplied to the driver.
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace SubtreeProofs.Rust.AssignmentDriverInvariant

open AssignmentColumnScan AssignmentScanInvariant AssignmentNumericBounds AssignmentSearchArithmetic AssignmentSearchInitialization
open AssignmentAugmentationMatching

structure Input (cost : Slice (alloc.vec.Vec I64)) (n extent : Usize) : Prop where
  n_size : n.val ≤ U32.max
  extent_eq : extent.val = n.val+1
  cost_len : cost.length = n.val
  square : ∀ row ∈ cost.val, row.length = cost.length
  initial_bounds : ∀ row, -costMagnitude ≤ initialRows cost n row ∧ initialRows cost n row ≤ costMagnitude

theorem Input.n_max (cost : Slice (alloc.vec.Vec I64)) (n extent : Usize) (h : Input cost n extent) : n.val < Usize.max := by
  have he := h.extent_eq
  scalar_tac

theorem Input.square_at (cost : Slice (alloc.vec.Vec I64)) (n extent : Usize) (h : Input cost n extent)
    (row : Nat) (hr : row < n.val) : (cost.val[row]!).length = n.val := by
  have hb : row < cost.length := by rw [h.cost_len]; exact hr
  have hm : cost.val[row]! ∈ cost.val := by
    rw [getElem!_pos cost.val row hb]
    exact List.getElem_mem hb
  exact (h.square _ hm).trans h.cost_len

structure Invariant (cost : Slice (alloc.vec.Vec I64)) (n : Usize)
    (u v : alloc.vec.Vec I128) (matched predecessor : alloc.vec.Vec Usize) (nextRow : Usize)
    (failure : Option verified_assignment_core.AssignmentError) : Prop where
  u_len : n.val < u.length
  v_len : n.val < v.length
  matched_len : n.val < matched.length
  predecessor_len : n.val < predecessor.length
  row_positive : 0 < nextRow.val
  row_bound : nextRow.val ≤ n.val+1
  failure_none : failure = none
  matching : Assignment.PartialRows n.val (nextRow.val-1) (pointers matched)
  potential : PotentialInvariant cost n (initialRows cost n) u v
  matching_tight : Assignment.TightPointers n.val (AssignmentReconstruction.pointerMatrix cost)
    (fun row => u.val[row]!.val) (fun col => v.val[col]!.val) (pointers matched)

abbrev DriverState := alloc.vec.Vec I128 × alloc.vec.Vec I128 × alloc.vec.Vec Usize × alloc.vec.Vec Usize × Usize ×
  Option verified_assignment_core.AssignmentError

abbrev DriverOutput := alloc.vec.Vec I128 × alloc.vec.Vec I128 × alloc.vec.Vec Usize × Option verified_assignment_core.AssignmentError

def StateInvariant (cost : Slice (alloc.vec.Vec I64)) (n : Usize) (state : DriverState) : Prop :=
  let (u,v,matched,predecessor,row,failure) := state
  Invariant cost n u v matched predecessor row failure

/-- Reserved zero is separate from every actual real-column pointer. -/
theorem set_root_real (matched : alloc.vec.Vec Usize) (n value : Usize) (hmatched : n.val < matched.length)
    (col : Nat) (hp : 0 < col) (hb : col ≤ n.val) : (matched.set 0#usize value).val[col]! = matched.val[col]! := by
  exact vec_set_other matched 0#usize value col (lt_of_le_of_lt hb hmatched) (by scalar_tac)

theorem set_root_matching (matched : alloc.vec.Vec Usize) (n value : Usize) (filled : Nat) (hmatched : n.val < matched.length)
    (hmatching : Assignment.PartialRows n.val filled (pointers matched)) :
    Assignment.PartialRows n.val filled (fun col => (alloc.vec.Vec.deref (matched.set 0#usize value)).val[col]!.val) := by
  apply hmatching.congr
  intro col hp hb
  simp only [alloc.vec.Vec.deref,Slice.from_val,pointers,set_root_real matched n value hmatched col hp hb]

theorem set_root_tight (cost : Slice (alloc.vec.Vec I64)) (u v : alloc.vec.Vec I128) (matched : alloc.vec.Vec Usize)
    (n value : Usize) (hmatched : n.val < matched.length)
    (htight : Assignment.TightPointers n.val (AssignmentReconstruction.pointerMatrix cost)
      (fun row => u.val[row]!.val) (fun col => v.val[col]!.val) (pointers matched)) :
    Assignment.TightPointers n.val (AssignmentReconstruction.pointerMatrix cost)
      (fun row => u.val[row]!.val) (fun col => v.val[col]!.val)
      (fun col => (alloc.vec.Vec.deref (matched.set 0#usize value)).val[col]!.val) := by
  apply htight.congr
  intro col hp hb
  simp only [alloc.vec.Vec.deref,Slice.from_val,pointers,set_root_real matched n value hmatched col hp hb]

/-- The source's reserved-pointer write establishes every independent input
property required by the complete actual search theorem. -/
theorem search_input (cost : Slice (alloc.vec.Vec I64)) (n extent : Usize) (input : Input cost n extent)
    (u v : alloc.vec.Vec I128) (matched predecessor : alloc.vec.Vec Usize) (nextRow : Usize)
    (h : Invariant cost n u v matched predecessor nextRow none) (hr : nextRow.val ≤ n.val) :
    AssignmentSearchInvariant.Input cost (alloc.vec.Vec.deref (matched.set 0#usize nextRow)) n extent (nextRow.val-1) (initialRows cost n) := by
  refine ⟨input.n_size,input.extent_eq,input.cost_len,input.square_at cost n extent,?_,by have hp := h.row_positive; omega,
    set_root_matching matched n nextRow _ h.matched_len h.matching,?_,input.initial_bounds⟩
  · simpa only [alloc.vec.Vec.deref,Slice.length,Slice.from_val,alloc.vec.Vec.length,alloc.vec.Vec.set_length] using h.matched_len
  · simp only [alloc.vec.Vec.deref,Slice.from_val]
    have hzero := vec_set_self matched 0#usize nextRow (by have hb := h.matched_len; scalar_tac)
    simp only [UScalar.ofNatCore_val_eq] at hzero
    rw [hzero]
    have hp := h.row_positive
    omega

end SubtreeProofs.Rust.AssignmentDriverInvariant

end
