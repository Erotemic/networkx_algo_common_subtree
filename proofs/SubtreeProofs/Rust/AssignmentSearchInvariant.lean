module

public import SubtreeProofs.Rust.AssignmentSearchInitialization
public import SubtreeProofs.Rust.AssignmentPredecessorTightness
public import SubtreeProofs.Rust.AssignmentVisitColumn
import Mathlib.Tactic

/-!
# Combined invariant for the actual alternating-tree search

The invariant combines independent feasible duals, exact objective accounting,
attained cut minima, partial-matching tightness, discovery ranks and pending
predecessor tightness. It also records the physical representation and source
failure/visit guards needed for a complete total-correctness loop proof.
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace SubtreeProofs.Rust.AssignmentSearchInvariant

open AssignmentColumnScan AssignmentScanInvariant AssignmentScanCut AssignmentAdjustmentInvariant
open AssignmentSearchCapacity AssignmentNumericBounds AssignmentSearchArithmetic AssignmentDiscoveryRanks
open AssignmentPredecessorPaths AssignmentPredecessorTightness AssignmentVisitColumn

structure Input (cost : Slice (alloc.vec.Vec I64)) (matched : Slice Usize) (n extent : Usize)
    (filled : Nat) (initialRows : Fin n.val → ℤ) : Prop where
  n_size : n.val ≤ U32.max
  extent_eq : extent.val = n.val+1
  cost_len : cost.length = n.val
  square : ∀ row < n.val, (cost.val[row]!).length = n.val
  matched_len : n.val < matched.length
  filled_lt : filled < n.val
  matching : Assignment.PartialRows n.val filled (fun col => matched.val[col]!.val)
  root : matched.val[0]!.val = filled+1
  initial_bounds : ∀ row, -costMagnitude ≤ initialRows row ∧ initialRows row ≤ costMagnitude

theorem Input.n_max (cost : Slice (alloc.vec.Vec I64)) (matched : Slice Usize) (n extent : Usize)
    (filled : Nat) (initialRows : Fin n.val → ℤ) (h : Input cost matched n extent filled initialRows) : n.val < Usize.max := by
  have he := h.extent_eq
  scalar_tac

structure Invariant (cost : Slice (alloc.vec.Vec I64)) (matched : Slice Usize) (n : Usize) (initialRows : Fin n.val → ℤ)
    (u v : alloc.vec.Vec I128) (predecessor : alloc.vec.Vec Usize) (column : Usize)
    (slack : alloc.vec.Vec (Option I128)) (used : alloc.vec.Vec Bool) (visited : Usize) (searching : Bool)
    (failure : Option verified_assignment_core.AssignmentError) : Prop where
  u_len : n.val < u.length
  v_len : n.val < v.length
  predecessor_len : n.val < predecessor.length
  slack_len : n.val < slack.length
  used_len : n.val < used.length
  failure_none : failure = none
  column_bound : column.val ≤ n.val
  column_free : used.val[column.val]! = false
  reserved : used.val[0]! = true ∨ column.val = 0
  visited_card : visited.val = (usedIndices (alloc.vec.Vec.deref used) (n.val+1)).card
  used_matched : UsedMatched matched (alloc.vec.Vec.deref used) n
  searching_exact : searching = true ↔ matched.val[column.val]!.val ≠ 0
  potential : PotentialInvariant cost n initialRows u v
  slacks : SlackInvariant cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) matched (alloc.vec.Vec.deref used)
    (usedIndices (alloc.vec.Vec.deref used) (n.val+1)) slack predecessor n
  matching_tight : Assignment.TightPointers n.val (AssignmentReconstruction.pointerMatrix cost)
    (fun row => u.val[row]!.val) (fun col => v.val[col]!.val) (fun col => matched.val[col]!.val)
  ranked : ∃ rank : Nat → Nat, DiscoveryBound (usedIndices (alloc.vec.Vec.deref used) (n.val+1)) rank visited.val ∧
    Ranked (alloc.vec.Vec.deref predecessor) n (usedIndices (alloc.vec.Vec.deref used) (n.val+1)) rank
  pending_predecessor : column.val ≠ 0 → predecessor.val[column.val]!.val ∈ usedIndices (alloc.vec.Vec.deref used) (n.val+1)
  forest_tight : ForestTight cost u v matched (alloc.vec.Vec.deref predecessor) (usedIndices (alloc.vec.Vec.deref used) (n.val+1))
  pending_tight : column.val ≠ 0 →
    u.val[matched.val[predecessor.val[column.val]!.val]!.val]!.val + v.val[column.val]!.val =
      AssignmentReconstruction.pointerMatrix cost matched.val[predecessor.val[column.val]!.val]!.val column.val

abbrev SearchState := alloc.vec.Vec I128 × alloc.vec.Vec I128 × alloc.vec.Vec Usize × Usize ×
  alloc.vec.Vec (Option I128) × alloc.vec.Vec Bool × Usize × Bool × Option verified_assignment_core.AssignmentError

abbrev SearchOutput := alloc.vec.Vec I128 × alloc.vec.Vec I128 × alloc.vec.Vec Usize × Usize ×
  Option verified_assignment_core.AssignmentError

def StateInvariant (cost : Slice (alloc.vec.Vec I64)) (matched : Slice Usize) (n : Usize)
    (initialRows : Fin n.val → ℤ) (state : SearchState) : Prop :=
  let (u,v,predecessor,column,slack,used,visited,searching,failure) := state
  Invariant cost matched n initialRows u v predecessor column slack used visited searching failure

/-- The source visit-limit test follows from the combined independent state. -/
theorem Invariant.visit_guard (cost : Slice (alloc.vec.Vec I64)) (matched : Slice Usize) (n extent : Usize)
    (filled : Nat) (initialRows : Fin n.val → ℤ) (input : Input cost matched n extent filled initialRows)
    (u v : alloc.vec.Vec I128) (predecessor : alloc.vec.Vec Usize) (column : Usize)
    (slack : alloc.vec.Vec (Option I128)) (used : alloc.vec.Vec Bool) (visited : Usize) (searching : Bool)
    (failure : Option verified_assignment_core.AssignmentError)
    (h : Invariant cost matched n initialRows u v predecessor column slack used visited searching failure)
    (hsearching : searching = true) : visited.val < n.val := by
  apply AssignmentSearchCapacity.visit_guard matched (alloc.vec.Vec.deref used) n filled visited column
    input.matching input.root input.filled_lt h.used_matched h.visited_card h.column_bound
    (h.searching_exact.mp hsearching)
  simpa only [alloc.vec.Vec.deref,Slice.from_val] using h.column_free

/-- After the physical visit mark, the combined invariant supplies all actual
scan representation bounds; its active row is a real nonzero matched pointer. -/
theorem Invariant.scan_bounds_after_mark (cost : Slice (alloc.vec.Vec I64)) (matched : Slice Usize) (n extent : Usize)
    (filled : Nat) (initialRows : Fin n.val → ℤ) (input : Input cost matched n extent filled initialRows)
    (u v : alloc.vec.Vec I128) (predecessor : alloc.vec.Vec Usize) (column : Usize)
    (slack : alloc.vec.Vec (Option I128)) (used : alloc.vec.Vec Bool) (visited : Usize) (searching : Bool)
    (failure : Option verified_assignment_core.AssignmentError)
    (h : Invariant cost matched n initialRows u v predecessor column slack used visited searching failure)
    (hsearching : searching = true) :
    ScanBounds cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) (alloc.vec.Vec.deref (used.set column true))
      slack predecessor n matched.val[column.val]! := by
  have hr := nonzero_pointer_bounds matched n filled column.val input.matching input.root input.filled_lt h.column_bound
    (h.searching_exact.mp hsearching)
  have hcostlen := input.cost_len
  refine ⟨input.n_max cost matched n extent filled initialRows,by omega,hr.1,hr.2,?_,?_,?_,?_,h.slack_len,h.predecessor_len⟩
  · rw [input.square (matched.val[column.val]!.val-1) (by omega)]
  · simpa only [alloc.vec.Vec.deref,Slice.length,Slice.from_val,alloc.vec.Vec.length] using h.u_len
  · simpa only [alloc.vec.Vec.deref,Slice.length,Slice.from_val,alloc.vec.Vec.length] using h.v_len
  · simpa only [alloc.vec.Vec.deref,Slice.length,Slice.from_val,alloc.vec.Vec.length,alloc.vec.Vec.set_length] using h.used_len

end SubtreeProofs.Rust.AssignmentSearchInvariant

end
