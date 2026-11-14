module

public import SubtreeProofs.Rust.AssignmentSearchAdjustment
import Mathlib.Tactic

/-!
# Initialization and continuation of the combined actual search invariant

Exact actual initializer contents establish the starting state. Exact scan
and adjustment results establish the next physical state, including visit
count, source search flag, represented arrays and the pending tight edge.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentSearchTransition

open AssignmentColumnScan AssignmentScanInvariant AssignmentScanCut AssignmentAdjustmentInvariant AssignmentSearchCapacity
open AssignmentNumericBounds AssignmentSearchArithmetic AssignmentSearchInvariant AssignmentVisitColumn AssignmentSearchInitialization
open AssignmentSearchScan AssignmentSearchAdjustment AssignmentDiscoveryRanks AssignmentPredecessorPaths AssignmentPredecessorTightness

/-- The exact contents proved for the actual two local initializer loops
establish every component of the initial search invariant. -/
theorem initial_invariant (cost : Slice (alloc.vec.Vec I64)) (matched : Slice Usize) (n extent : Usize)
    (filled : Nat) (initialRows : Fin n.val → ℤ) (input : Input cost matched n extent filled initialRows)
    (u v : alloc.vec.Vec I128) (predecessor : alloc.vec.Vec Usize) (slack : alloc.vec.Vec (Option I128)) (used : alloc.vec.Vec Bool)
    (hu : n.val < u.length) (hv : n.val < v.length) (hp : n.val < predecessor.length)
    (hslack : slack.val = List.replicate extent.val none) (hused : used.val = List.replicate extent.val false)
    (hpotential : PotentialInvariant cost n initialRows u v)
    (htight : Assignment.TightPointers n.val (AssignmentReconstruction.pointerMatrix cost)
      (fun row => u.val[row]!.val) (fun col => v.val[col]!.val) (fun col => matched.val[col]!.val)) :
    Invariant cost matched n initialRows u v predecessor 0#usize slack used 0#usize true none := by
  have hs : slack.val = List.replicate (n.val+1) none := by simpa only [input.extent_eq] using hslack
  have hf : used.val = List.replicate (n.val+1) false := by simpa only [input.extent_eq] using hused
  have he := initial_usedIndices used n hf
  refine {
    u_len := hu, v_len := hv, predecessor_len := hp,
    slack_len := ?_, used_len := ?_, failure_none := rfl,
    column_bound := by simp, column_free := by simp [hf], reserved := Or.inr (by simp),
    visited_card := by simp [he], used_matched := ?_, searching_exact := ?_,
    potential := hpotential, slacks := ?_, matching_tight := htight,
    ranked := ?_, pending_predecessor := by simp, forest_tight := ?_, pending_tight := by simp }
  · change n.val < slack.val.length
    rw [hs,List.length_replicate]
    omega
  · change n.val < used.val.length
    rw [hf,List.length_replicate]
    omega
  · intro col hb hflag
    simp [alloc.vec.Vec.deref,Slice.from_val,hf] at hflag
  · simp only [eq_self,true_iff,UScalar.ofNatCore_val_eq]
    rw [input.root]
    omega
  · rw [he]
    exact initial_slackInvariant cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) matched (alloc.vec.Vec.deref used) slack predecessor n hs
  · refine ⟨fun _ => 0,?_,?_⟩
    · rw [he]
      exact discovery_initial
    · rw [he]
      simp [Ranked]
  · rw [he]
    simp [ForestTight]

/-- The source's nonzero-pointer boolean agrees exactly with the independent
natural pointer test, including reserved machine representation. -/
theorem search_flag (matched : Slice Usize) (column : Usize) :
    (matched.val[column.val]! != 0#usize) = true ↔ matched.val[column.val]!.val ≠ 0 := by
  simp [bne_iff_ne,UScalar.eq_equiv]

/-- The exact successful subphase results reestablish every invariant field
for the next actual loop state. -/
theorem next_invariant (cost : Slice (alloc.vec.Vec I64)) (matched : Slice Usize) (n : Usize)
    (initialRows : Fin n.val → ℤ)
    (u v : alloc.vec.Vec I128) (predecessor : alloc.vec.Vec Usize) (column : Usize)
    (slack : alloc.vec.Vec (Option I128)) (used : alloc.vec.Vec Bool) (visited : Usize)
    (h : Invariant cost matched n initialRows u v predecessor column slack used visited true none)
    (amount : I128) (selected : Usize) (newSlack : alloc.vec.Vec (Option I128)) (newPred : alloc.vec.Vec Usize)
    (hscan : Scanned cost u v matched (used.set column true) slack predecessor column n amount selected newSlack newPred)
    (newU newV : alloc.vec.Vec I128) (finalSlack : alloc.vec.Vec (Option I128))
    (hadjust : Adjusted cost matched n initialRows u v (used.set column true) newSlack newPred amount selected (visited.val+1)
      (core.result.Result.Ok (),newU,newV,finalSlack)) (nextVisited : Usize) (hvisited : nextVisited.val = visited.val+1) :
    Invariant cost matched n initialRows newU newV newPred selected finalSlack (used.set column true) nextVisited
      (matched.val[selected.val]! != 0#usize) none := by
  refine {
    u_len := ?_, v_len := ?_, predecessor_len := ?_, slack_len := ?_, used_len := ?_, failure_none := rfl,
    column_bound := hscan.selected_bound, column_free := hscan.selected_free, reserved := ?_, visited_card := ?_,
    used_matched := ?_, searching_exact := search_flag matched selected,
    potential := hadjust.potential, slacks := hadjust.slacks, matching_tight := hadjust.matching_tight,
    ranked := ?_, pending_predecessor := fun _ => hscan.predecessor_member,
    forest_tight := hadjust.forest_tight, pending_tight := fun _ => hadjust.pending_tight }
  · have he := hadjust.complete.2.1.1
    dsimp only at he
    rw [he]
    exact h.u_len
  · have he := hadjust.complete.2.2.1.1
    dsimp only at he
    rw [he]
    exact h.v_len
  · rw [hscan.predecessor_frame.1]
    exact h.predecessor_len
  · have he := hadjust.complete.2.2.2.1
    dsimp only at he
    rw [he,hscan.slack_frame.1]
    exact h.slack_len
  · simpa using h.used_len
  · exact Or.inl (mark_reserved used n column h.used_len h.column_bound h.reserved)
  · rw [mark_cardinality used n column h.used_len h.column_bound h.column_free,← h.visited_card]
    exact hvisited
  · exact mark_matched matched used n column h.used_len h.column_bound h.used_matched (h.searching_exact.mp rfl)
  · simpa only [hvisited] using hadjust.ranked

end SubtreeProofs.Rust.AssignmentSearchTransition

end
