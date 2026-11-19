module

public import SubtreeProofs.Rust.AssignmentSearchScan
import Mathlib.Tactic

/-!
# Actual potential adjustment from a complete search scan

A visited candidate set retains a ranked tight predecessor forest through
actual scanning and adjustment. The source update preserves the numeric,
cut and old matching invariants and establishes the selected pending edge.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentSearchAdjustment

open AssignmentColumnScan AssignmentScanInvariant AssignmentScanCut AssignmentAdjustment AssignmentAdjustmentInvariant AssignmentAdjustmentLoop
open AssignmentSearchCapacity AssignmentNumericBounds AssignmentSearchArithmetic AssignmentSearchInvariant AssignmentVisitColumn
open AssignmentSearchScan AssignmentSafeAdjustment AssignmentDiscoveryRanks AssignmentPredecessorPaths
open AssignmentAdjustmentTightness AssignmentPredecessorTightness

structure Adjusted (cost : Slice (alloc.vec.Vec I64)) (matched : Slice Usize) (n : Usize) (initialRows : Fin n.val → ℤ)
    (u v : alloc.vec.Vec I128) (used : alloc.vec.Vec Bool) (slack : alloc.vec.Vec (Option I128))
    (predecessor : alloc.vec.Vec Usize) (amount : I128) (selected : Usize) (visited : Nat) (output : AdjustOutput) : Prop where
  complete : CompleteAdjustment u v matched (alloc.vec.Vec.deref used) slack amount n output
  bounds : Bounds u v matched (alloc.vec.Vec.deref used) slack amount n
  potential : PotentialInvariant cost n initialRows output.2.1 output.2.2.1
  slacks : SlackInvariant cost (alloc.vec.Vec.deref output.2.1) (alloc.vec.Vec.deref output.2.2.1) matched (alloc.vec.Vec.deref used)
    (usedIndices (alloc.vec.Vec.deref used) (n.val+1)) output.2.2.2 predecessor n
  matching_tight : Assignment.TightPointers n.val (AssignmentReconstruction.pointerMatrix cost)
    (fun row => output.2.1.val[row]!.val) (fun col => output.2.2.1.val[col]!.val) (fun col => matched.val[col]!.val)
  ranked : ∃ rank : Nat → Nat, DiscoveryBound (usedIndices (alloc.vec.Vec.deref used) (n.val+1)) rank visited ∧
    Ranked (alloc.vec.Vec.deref predecessor) n (usedIndices (alloc.vec.Vec.deref used) (n.val+1)) rank
  forest_tight : ForestTight cost output.2.1 output.2.2.1 matched (alloc.vec.Vec.deref predecessor) (usedIndices (alloc.vec.Vec.deref used) (n.val+1))
  pending_tight : output.2.1.val[matched.val[predecessor.val[selected.val]!.val]!.val]!.val + output.2.2.1.val[selected.val]!.val =
    AssignmentReconstruction.pointerMatrix cost matched.val[predecessor.val[selected.val]!.val]!.val selected.val

/-- Successful complete scanning supplies the actual adjustment's input.
All arithmetic is derived from the search invariant and candidate minima;
matching tightness, ranked forest and the new pending edge are preserved. -/
theorem adjustment_from_scan_spec (cost : Slice (alloc.vec.Vec I64)) (matched : Slice Usize) (n extent : Usize)
    (filled : Nat) (initialRows : Fin n.val → ℤ) (input : Input cost matched n extent filled initialRows)
    (u v : alloc.vec.Vec I128) (predecessor : alloc.vec.Vec Usize) (column : Usize)
    (slack : alloc.vec.Vec (Option I128)) (used : alloc.vec.Vec Bool) (visited : Usize) (searching : Bool)
    (failure : Option AssignmentError)
    (h : Invariant cost matched n initialRows u v predecessor column slack used visited searching failure)
    (hsearching : searching = true) (amount : I128) (selected : Usize)
    (newSlack : alloc.vec.Vec (Option I128)) (newPred : alloc.vec.Vec Usize)
    (hscan : Scanned cost u v matched (used.set column true) slack predecessor column n amount selected newSlack newPred) :
    adjust_potentials u v matched (alloc.vec.Vec.deref (used.set column true)) newSlack amount n ⦃ output =>
      Adjusted cost matched n initialRows u v (used.set column true) newSlack newPred amount selected (visited.val+1) output ⦄ := by
  let marked := used.set column true
  let candidates := usedIndices (alloc.vec.Vec.deref used) (n.val+1)
  let newCandidates := usedIndices (alloc.vec.Vec.deref marked) (n.val+1)
  have hset : newCandidates = insert column.val candidates := usedIndices_set_true used n column h.column_bound h.used_len
  have hmarked := mark_matched matched used n column h.used_len h.column_bound h.used_matched (h.searching_exact.mp hsearching)
  have hinjective := used_injective matched (alloc.vec.Vec.deref marked) n filled input.matching input.root hmarked
  have hzero : (alloc.vec.Vec.deref marked).val[0]! = true := by
    simpa only [marked,alloc.vec.Vec.deref,Slice.from_val] using mark_reserved used n column h.used_len h.column_bound h.reserved
  have hrows : ∀ col, col ≤ n.val → (alloc.vec.Vec.deref marked).val[col]! = true →
      0 < matched.val[col]!.val ∧ matched.val[col]!.val ≤ n.val := by
    intro col hb hf
    exact nonzero_pointer_bounds matched n filled col input.matching input.root input.filled_lt hb (hmarked col hb hf)
  have hrepresentation : Representation u v matched (alloc.vec.Vec.deref marked) newSlack n := by
    refine ⟨input.n_max cost matched n extent filled initialRows,input.n_size,input.matched_len,?_,h.u_len,h.v_len,?_⟩
    · simpa only [marked,alloc.vec.Vec.deref,Slice.length,Slice.from_val,alloc.vec.Vec.length,alloc.vec.Vec.set_length] using h.used_len
    · rw [hscan.slack_frame.1]
      exact h.slack_len
  obtain ⟨rank,hdiscovery,hforest⟩ := h.ranked
  have hnew : column.val ∉ candidates := by
    intro hm
    have hh := (mem_usedIndices (alloc.vec.Vec.deref used) _ _).mp hm
    simp only [alloc.vec.Vec.deref,Slice.from_val,h.column_free] at hh
    exact Bool.noConfusion hh.2
  let newRank := advanceRank newCandidates rank (visited.val+1)
  have hdiscoveryNew : DiscoveryBound newCandidates newRank (visited.val+1) := by
    simpa only [newRank,hset] using discovery_visit candidates rank visited.val column.val hdiscovery hnew
  have hforestMarked : Ranked (alloc.vec.Vec.deref predecessor) n newCandidates newRank := by
    simpa only [newRank,hset] using ranked_visit (alloc.vec.Vec.deref predecessor) n candidates rank visited.val column.val
      hforest hdiscovery h.column_bound hnew (by
        intro hz
        simpa only [candidates,alloc.vec.Vec.deref,Slice.from_val] using h.pending_predecessor hz)
  have hforestNew := scan_preserves_forest (alloc.vec.Vec.deref marked) _ slack predecessor newPred column n newRank
    h.predecessor_len hforestMarked hscan.predecessor_frame
  have htightMarked : ForestTight cost u v matched (alloc.vec.Vec.deref predecessor) newCandidates := by
    rw [hset]
    apply forest_visit cost u v matched (alloc.vec.Vec.deref predecessor) candidates column.val h.forest_tight
    intro hz
    simpa only [alloc.vec.Vec.deref,Slice.from_val] using h.pending_tight hz
  have htightNew := scan_forest_tight cost u v matched (alloc.vec.Vec.deref marked) _ slack predecessor newPred column n
    h.predecessor_len hscan.predecessor_frame htightMarked
  apply WP.spec_mono (adjust_potentials_from_search_spec cost u v matched (alloc.vec.Vec.deref marked) newSlack newPred amount n
    hrepresentation initialRows input.initial_bounds h.potential hscan.nonnegative hinjective hzero hrows hscan.slacks (by
      intro target hp hb hf candidate hc
      exact hscan.minimum target hp hb (by simpa only [alloc.vec.Vec.deref,Slice.from_val] using hf) candidate hc))
  rintro output ⟨hcomplete,hpotential,hslacks,hbounds⟩
  refine ⟨hcomplete,hbounds,hpotential,hslacks,?_,⟨newRank,hdiscoveryNew,hforestNew⟩,?_,?_⟩
  · exact complete_matching_tight cost u v matched (alloc.vec.Vec.deref marked) newSlack amount n output filled
      h.u_len h.v_len hcomplete input.matching (Nat.le_of_lt input.filled_lt) input.root h.matching_tight
  · exact adjustment_forest_tight cost u v matched (alloc.vec.Vec.deref newPred) (alloc.vec.Vec.deref marked) newSlack amount n output
      hbounds hcomplete newRank hforestNew htightNew
  · have hselected := selected_predecessor_tight cost u v matched (alloc.vec.Vec.deref newPred) (alloc.vec.Vec.deref marked) newSlack amount n output
      hbounds hcomplete selected.val hscan.selected_bound
      (by simpa only [alloc.vec.Vec.deref,Slice.from_val] using hscan.selected_free)
      (by simpa only [alloc.vec.Vec.deref,Slice.from_val] using hscan.predecessor_member)
      (by simpa only [alloc.vec.Vec.deref,Slice.from_val] using hscan.attained)
    simpa only [alloc.vec.Vec.deref,Slice.from_val] using hselected

end SubtreeProofs.Rust.AssignmentSearchAdjustment

end
