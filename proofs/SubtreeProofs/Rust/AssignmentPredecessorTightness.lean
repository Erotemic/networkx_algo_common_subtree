module

public import SubtreeProofs.Rust.AssignmentDiscoveryRanks
public import SubtreeProofs.Rust.AssignmentAdjustmentTightness
import Mathlib.Tactic

/-!
# Tight predecessor forests through actual scan and adjustment

Visiting the pending column extends the tight forest. Exact actual scan
frames preserve its already visited predecessor links. Actual adjustment
preserves those edges and makes the selected attaining predecessor edge tight.
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace SubtreeProofs.Rust.AssignmentPredecessorTightness

open AssignmentColumnScan AssignmentScanInvariant AssignmentScanCut AssignmentAdjustment AssignmentAdjustmentInvariant
open AssignmentAdjustmentLoop AssignmentPredecessorPaths AssignmentDiscoveryRanks AssignmentAdjustmentTightness

def ForestTight (cost : Slice (alloc.vec.Vec I64)) (u v : alloc.vec.Vec I128) (matched predecessor : Slice Usize)
    (vertices : Finset Nat) : Prop :=
  ∀ col ∈ vertices, col ≠ 0 →
    u.val[matched.val[predecessor.val[col]!.val]!.val]!.val + v.val[col]!.val =
      AssignmentReconstruction.pointerMatrix cost matched.val[predecessor.val[col]!.val]!.val col

theorem forest_visit (cost : Slice (alloc.vec.Vec I64)) (u v : alloc.vec.Vec I128) (matched predecessor : Slice Usize)
    (vertices : Finset Nat) (column : Nat) (hforest : ForestTight cost u v matched predecessor vertices)
    (hpending : column ≠ 0 →
      u.val[matched.val[predecessor.val[column]!.val]!.val]!.val + v.val[column]!.val =
        AssignmentReconstruction.pointerMatrix cost matched.val[predecessor.val[column]!.val]!.val column) :
    ForestTight cost u v matched predecessor (insert column vertices) := by
  intro col hc hz
  rcases Finset.mem_insert.mp hc with he | hm
  · subst col
    exact hpending hz
  · exact hforest col hm hz

/-- The actual source's unchanged used-column predecessor slots preserve
every visited forest edge during the complete column scan. -/
theorem scan_forest_tight (cost : Slice (alloc.vec.Vec I64)) (u v : alloc.vec.Vec I128) (matched : Slice Usize)
    (used : Slice Bool) (weights : Nat → WithTop ℤ) (slack : alloc.vec.Vec (Option I128))
    (predecessor newPred : alloc.vec.Vec Usize) (column n : Usize) (hplen : n.val < predecessor.length)
    (hframe : PredecessorPrefix used weights slack predecessor newPred column (n.val+1))
    (hforest : ForestTight cost u v matched (alloc.vec.Vec.deref predecessor) (usedIndices used (n.val+1))) :
    ForestTight cost u v matched (alloc.vec.Vec.deref newPred) (usedIndices used (n.val+1)) := by
  intro col hc hz
  have he := scan_predecessor_unchanged used weights slack predecessor newPred column n hplen hframe col hc
  simp only [alloc.vec.Vec.deref,Slice.from_val]
  rw [he]
  simpa only [alloc.vec.Vec.deref,Slice.from_val] using hforest col hc hz

/-- Actual potential array writes preserve the visited tight predecessor
forest. Rankedness supplies predecessor membership in the visited cut. -/
theorem adjustment_forest_tight (cost : Slice (alloc.vec.Vec I64)) (u v : alloc.vec.Vec I128)
    (matched predecessor : Slice Usize) (used : Slice Bool) (slack : alloc.vec.Vec (Option I128))
    (amount : I128) (n : Usize) (output : AdjustOutput) (bounds : Bounds u v matched used slack amount n)
    (hcomplete : CompleteAdjustment u v matched used slack amount n output) (rank : Nat → Nat)
    (hranked : Ranked predecessor n (usedIndices used (n.val+1)) rank)
    (hforest : ForestTight cost u v matched predecessor (usedIndices used (n.val+1))) :
    ForestTight cost output.2.1 output.2.2.1 matched predecessor (usedIndices used (n.val+1)) := by
  intro col hc hz
  have hp := (hranked.2 col hc hz).1
  exact complete_visited_edge u v matched used slack amount n output bounds hcomplete predecessor.val[col]!.val col hp hc
    (AssignmentReconstruction.pointerMatrix cost matched.val[predecessor.val[col]!.val]!.val col) (hforest col hc hz)

/-- The selected unused column acquires the exact tight predecessor equation
needed to become the next visited column or the terminal augmentation vertex. -/
theorem selected_predecessor_tight (cost : Slice (alloc.vec.Vec I64)) (u v : alloc.vec.Vec I128)
    (matched predecessor : Slice Usize) (used : Slice Bool) (slack : alloc.vec.Vec (Option I128))
    (amount : I128) (n : Usize) (output : AdjustOutput) (bounds : Bounds u v matched used slack amount n)
    (hcomplete : CompleteAdjustment u v matched used slack amount n output) (selected : Nat)
    (hb : selected ≤ n.val) (hfree : used.val[selected]! = false)
    (hc : predecessor.val[selected]!.val ∈ usedIndices used (n.val+1))
    (hattained : amount.val = candidateCost cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) matched selected predecessor.val[selected]!.val) :
    output.2.1.val[matched.val[predecessor.val[selected]!.val]!.val]!.val + output.2.2.1.val[selected]!.val =
      AssignmentReconstruction.pointerMatrix cost matched.val[predecessor.val[selected]!.val]!.val selected := by
  have hz := complete_selected_edge cost u v matched used slack amount n output bounds hcomplete
    selected predecessor.val[selected]!.val hb hfree hc hattained
  simp only [candidateCost,reducedAt,alloc.vec.Vec.deref,Slice.from_val] at hz
  unfold AssignmentReconstruction.pointerMatrix
  linarith

end SubtreeProofs.Rust.AssignmentPredecessorTightness

end
