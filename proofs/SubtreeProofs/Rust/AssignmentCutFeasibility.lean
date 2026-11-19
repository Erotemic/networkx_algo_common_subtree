module

public import SubtreeProofs.Rust.AssignmentScanCut
public import SubtreeProofs.Rust.AssignmentAdjustmentFeasibility
public import SubtreeProofs.Rust.AssignmentReconstruction
public import SubtreeProofs.Shared.AssignmentSearchCapacity
import Mathlib.Tactic

/-!
# Deriving cut feasibility and matching lockstep from actual search views

These bridges convert the actual scan's attained candidate-cost bounds into
the independent finite matrix cut premises. They also derive the endpoint
lockstep property for every matched edge from partial-pointer injectivity.
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace SubtreeProofs.Rust.AssignmentCutFeasibility

open AssignmentColumnScan AssignmentScanInvariant AssignmentScanCut AssignmentAdjustmentInvariant AssignmentAdjustmentFeasibility

/-- Feasible real potentials make every real candidate reduced cost
nonnegative, without assuming a nonnegative input matrix. -/
theorem candidateCost_nonnegative (cost : Slice (alloc.vec.Vec I64)) (u v : alloc.vec.Vec I128)
    (matched : Slice Usize) (n : Usize) (target candidate : Nat)
    (htp : 0 < target) (htb : target ≤ n.val)
    (hrp : 0 < matched.val[candidate]!.val) (hrb : matched.val[candidate]!.val ≤ n.val)
    (hfeasible : Assignment.Feasible (AssignmentReconstruction.matrix cost n) (potential n u) (potential n v)) :
    0 ≤ candidateCost cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) matched target candidate := by
  let row : Fin n.val := ⟨matched.val[candidate]!.val-1,by omega⟩
  let col : Fin n.val := ⟨target-1,by omega⟩
  have h := hfeasible row col
  have hrow : row.val+1 = matched.val[candidate]!.val := by dsimp only [row]; omega
  have hcol : col.val+1 = target := by dsimp only [col]; omega
  simp only [potential,hrow,hcol,AssignmentReconstruction.matrix,row,col] at h
  simp only [candidateCost,reducedAt,alloc.vec.Vec.deref,Slice.from_val]
  linarith

/-- The scan's attaining predecessor identifies a real cut edge, so dual
feasibility supplies nonnegativity of the actual chosen scalar adjustment. -/
theorem attained_nonnegative (cost : Slice (alloc.vec.Vec I64)) (u v : alloc.vec.Vec I128)
    (matched : Slice Usize) (n : Usize) (amount : I128) (target candidate : Nat)
    (htp : 0 < target) (htb : target ≤ n.val)
    (hrp : 0 < matched.val[candidate]!.val) (hrb : matched.val[candidate]!.val ≤ n.val)
    (hfeasible : Assignment.Feasible (AssignmentReconstruction.matrix cost n) (potential n u) (potential n v))
    (hattained : amount.val = candidateCost cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) matched target candidate) :
    0 ≤ amount.val := by
  rw [hattained]
  exact candidateCost_nonnegative cost u v matched n target candidate htp htb hrp hrb hfeasible

/-- Lower bounds on every actual candidate reduced cost are precisely the
independent finite cut premise required by feasibility preservation. -/
theorem candidate_lower_cut (cost : Slice (alloc.vec.Vec I64)) (u v : alloc.vec.Vec I128)
    (matched : Slice Usize) (used : Slice Bool) (amount : I128) (n : Usize)
    (hlower : ∀ target, 0 < target → target ≤ n.val → used.val[target]! = false →
      ∀ candidate ∈ usedIndices used (n.val+1), amount.val ≤
        candidateCost cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) matched target candidate) :
    ∀ row ∈ selectedRows n matched used, ∀ col, col ∉ selectedColumns n used →
      amount.val ≤ AssignmentReconstruction.matrix cost n row col - potential n u row - potential n v col := by
  intro row hr col hc
  have hrm := (mem_selectedRows n matched used row).mp hr
  obtain ⟨candidate,hb,hu,he⟩ := (mem_usedRows matched used _ _).mp hrm
  have hcm : col.val+1 ∉ usedIndices used (n.val+1) := fun hm => hc ((mem_selectedColumns n used col).mpr hm)
  have hfree : used.val[col.val+1]! = false := by
    cases hf : used.val[col.val+1]!
    · rfl
    · exact False.elim (hcm ((mem_usedIndices used _ _).mpr ⟨by have h := col.isLt; omega,hf⟩))
  have hlo := hlower (col.val+1) (by omega) (by have h := col.isLt; omega) hfree candidate
    ((mem_usedIndices used _ _).mpr ⟨hb,hu⟩)
  simpa only [candidateCost,reducedAt,alloc.vec.Vec.deref,Slice.from_val,he,Nat.add_sub_cancel,
    AssignmentReconstruction.matrix,potential] using hlo

/-- Every old matching edge has both endpoints selected together. An image
row can arise only from that same column, by the independent matching's
injectivity extended to reserved column zero. -/
theorem matched_lockstep (matched : Slice Usize) (used : Slice Bool) (n : Usize) (filled : Nat)
    (hpartial : Assignment.PartialRows n.val filled (fun col => matched.val[col]!.val))
    (hroot : matched.val[0]!.val = filled+1) (row col : Fin n.val)
    (hpair : matched.val[col.val+1]!.val = row.val+1) :
    row ∈ selectedRows n matched used ↔ col ∈ selectedColumns n used := by
  constructor
  · intro hr
    obtain ⟨candidate,hb,hu,he⟩ := (mem_usedRows matched used _ _).mp ((mem_selectedRows n matched used row).mp hr)
    have hcandidate : candidate ≤ n.val := by omega
    have hcol : col.val+1 ≤ n.val := by have h := col.isLt; omega
    have hnonzero : matched.val[candidate]!.val ≠ 0 := by rw [he]; omega
    have hsame := hpartial.with_root_injective hroot candidate hcandidate hnonzero (col.val+1) hcol (he.trans hpair.symm)
    apply (mem_selectedColumns n used col).mpr
    apply (mem_usedIndices used _ _).mpr
    exact ⟨by have h := col.isLt; omega,by simpa only [hsame] using hu⟩
  · intro hc
    have hm := (mem_usedIndices used _ _).mp ((mem_selectedColumns n used col).mp hc)
    apply (mem_selectedRows n matched used row).mpr
    exact (mem_usedRows matched used _ _).mpr ⟨col.val+1,hm.1,hm.2,hpair⟩

end SubtreeProofs.Rust.AssignmentCutFeasibility

end
