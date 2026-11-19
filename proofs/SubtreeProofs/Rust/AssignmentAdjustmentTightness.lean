module

public import SubtreeProofs.Rust.AssignmentAdjustmentCut
public import SubtreeProofs.Rust.AssignmentCutFeasibility
import Mathlib.Tactic

/-!
# Actual adjustment preserves matching and visited predecessor tightness

Independent partial-pointer injectivity supplies matching endpoint lockstep.
Visited predecessor edges have both endpoints adjusted and remain tight; an
attaining edge into the selected unused column gains zero actual reduced cost.
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace SubtreeProofs.Rust.AssignmentAdjustmentTightness

open AssignmentColumnScan AssignmentScanInvariant AssignmentScanCut AssignmentAdjustment AssignmentAdjustmentInvariant
open AssignmentAdjustmentLoop AssignmentAdjustmentFeasibility AssignmentCutFeasibility AssignmentAdjustmentCut

/-- Every existing matching edge stays tight in the actual returned vectors;
endpoint lockstep is derived from the partial matching, rather than assumed. -/
theorem complete_matching_tight (cost : Slice (alloc.vec.Vec I64)) (u v : alloc.vec.Vec I128)
    (matched : Slice Usize) (used : Slice Bool) (slack : alloc.vec.Vec (Option I128))
    (amount : I128) (n : Usize) (output : AdjustOutput) (filled : Nat)
    (hu : n.val < u.length) (hv : n.val < v.length)
    (hcomplete : CompleteAdjustment u v matched used slack amount n output)
    (hpartial : Assignment.PartialRows n.val filled (fun col => matched.val[col]!.val))
    (hfilled : filled ≤ n.val) (hroot : matched.val[0]!.val = filled+1)
    (htight : Assignment.TightPointers n.val (AssignmentReconstruction.pointerMatrix cost)
      (fun row => u.val[row]!.val) (fun col => v.val[col]!.val) (fun col => matched.val[col]!.val)) :
    Assignment.TightPointers n.val (AssignmentReconstruction.pointerMatrix cost)
      (fun row => output.2.1.val[row]!.val) (fun col => output.2.2.1.val[col]!.val) (fun col => matched.val[col]!.val) := by
  intro column hp hb hn
  dsimp only at hn ⊢
  have hrp : 0 < matched.val[column]!.val := by omega
  have hrb : matched.val[column]!.val ≤ n.val := (hpartial.bound column hp hb).trans hfilled
  let row : Fin n.val := ⟨matched.val[column]!.val-1,by omega⟩
  let col : Fin n.val := ⟨column-1,by omega⟩
  have hri : row.val+1 = matched.val[column]!.val := by dsimp only [row]; omega
  have hci : col.val+1 = column := by dsimp only [col]; omega
  have hpair : matched.val[col.val+1]!.val = row.val+1 := by rw [hci,hri]
  have hlock := matched_lockstep matched used n filled hpartial hroot row col hpair
  have hold : potential n u row + potential n v col = AssignmentReconstruction.matrix cost n row col := by
    change u.val[row.val+1]!.val + v.val[col.val+1]!.val = (cost.val[row.val]!).val[col.val]!.val
    rw [hri,hci]
    exact htight column hp hb hn
  have h := complete_preserves_tight_edge u v matched used slack amount n output (AssignmentReconstruction.matrix cost n)
    hu hv hcomplete row col hold hlock
  change output.2.1.val[row.val+1]!.val + output.2.2.1.val[col.val+1]!.val = (cost.val[row.val]!).val[col.val]!.val at h
  rw [hri,hci] at h
  exact h

/-- A visited predecessor edge has both its candidate row and target column
adjusted; the actual array writes cancel exactly in its tightness equation. -/
theorem complete_visited_edge (u v : alloc.vec.Vec I128) (matched : Slice Usize) (used : Slice Bool)
    (slack : alloc.vec.Vec (Option I128)) (amount : I128) (n : Usize) (output : AdjustOutput)
    (bounds : Bounds u v matched used slack amount n) (hcomplete : CompleteAdjustment u v matched used slack amount n output)
    (candidate target : Nat) (hc : candidate ∈ usedIndices used (n.val+1)) (ht : target ∈ usedIndices used (n.val+1))
    (edgeCost : ℤ) (htight : u.val[matched.val[candidate]!.val]!.val + v.val[target]!.val = edgeCost) :
    output.2.1.val[matched.val[candidate]!.val]!.val + output.2.2.1.val[target]!.val = edgeCost := by
  have hcandidate := (mem_usedIndices used _ _).mp hc
  have htarget := (mem_usedIndices used _ _).mp ht
  have hrowBound := bounds.row_bound candidate (by omega) hcandidate.2
  have hrowMem : matched.val[candidate]!.val ∈ usedRows matched used (n.val+1) :=
    (mem_usedRows matched used _ _).mpr ⟨candidate,hcandidate.1,hcandidate.2,rfl⟩
  have hr := hcomplete.2.1.2 matched.val[candidate]!.val hrowBound
  have hcolBound : target < v.length := by have h := bounds.v_len; omega
  have hv := hcomplete.2.2.1.2 target hcolBound
  simp only [rowExpected,hrowMem,↓reduceIte] at hr
  simp only [columnExpected,ht,↓reduceIte] at hv
  rw [hr,hv]
  linarith

/-- The attaining predecessor at the selected unused column has zero reduced
cost in the actual returned potential vectors. -/
theorem complete_selected_edge (cost : Slice (alloc.vec.Vec I64)) (u v : alloc.vec.Vec I128)
    (matched : Slice Usize) (used : Slice Bool) (slack : alloc.vec.Vec (Option I128))
    (amount : I128) (n : Usize) (output : AdjustOutput) (bounds : Bounds u v matched used slack amount n)
    (hcomplete : CompleteAdjustment u v matched used slack amount n output)
    (target candidate : Nat) (ht : target ≤ n.val) (hfree : used.val[target]! = false)
    (hc : candidate ∈ usedIndices used (n.val+1))
    (hattained : amount.val = candidateCost cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) matched target candidate) :
    candidateCost cost (alloc.vec.Vec.deref output.2.1) (alloc.vec.Vec.deref output.2.2.1) matched target candidate = 0 := by
  rw [complete_candidateCost cost u v matched used slack amount n output bounds hcomplete target candidate ht hfree hc,← hattained]
  exact sub_self _

end SubtreeProofs.Rust.AssignmentAdjustmentTightness

end
