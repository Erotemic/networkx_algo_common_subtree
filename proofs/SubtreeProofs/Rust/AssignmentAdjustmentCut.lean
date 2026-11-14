module

public import SubtreeProofs.Rust.AssignmentScanCut
public import SubtreeProofs.Rust.AssignmentAdjustmentLoop
import Mathlib.Tactic

/-!
# Actual potential adjustment maintains all cut minima and predecessors

For an unused target, every used candidate row increases by the adjustment,
while the target's column potential is unchanged. All candidate reduced
costs therefore decrease by the same amount as the physical slack. The
predecessor vector is unchanged by adjustment and continues to attain it.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentAdjustmentCut

open AssignmentColumnScan AssignmentScanInvariant AssignmentScanCut AssignmentAdjustment AssignmentAdjustmentInvariant AssignmentAdjustmentLoop

/-- Every cut candidate's actual reduced cost loses exactly the adjustment
at every real unused target, as specified by the returned vector frame. -/
theorem complete_candidateCost (cost : Slice (alloc.vec.Vec I64)) (u v : alloc.vec.Vec I128)
    (matched : Slice Usize) (used : Slice Bool) (slack : alloc.vec.Vec (Option I128))
    (amount : I128) (n : Usize) (output : AdjustOutput) (bounds : Bounds u v matched used slack amount n)
    (hcomplete : CompleteAdjustment u v matched used slack amount n output)
    (target candidate : Nat) (ht : target ≤ n.val) (hfree : used.val[target]! = false)
    (hc : candidate ∈ usedIndices used (n.val+1)) :
    candidateCost cost (alloc.vec.Vec.deref output.2.1) (alloc.vec.Vec.deref output.2.2.1) matched target candidate =
      candidateCost cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) matched target candidate - amount.val := by
  have hcandidate := (mem_usedIndices used (n.val+1) candidate).mp hc
  have hcle : candidate ≤ n.val := by omega
  have hrowBound := bounds.row_bound candidate hcle hcandidate.2
  have hrowMem : matched.val[candidate]!.val ∈ usedRows matched used (n.val+1) :=
    (mem_usedRows matched used _ _).mpr ⟨candidate,hcandidate.1,hcandidate.2,rfl⟩
  have hrow := hcomplete.2.1.2 matched.val[candidate]!.val hrowBound
  simp only [rowExpected,hrowMem,↓reduceIte] at hrow
  have htargetNot : target ∉ usedIndices used (n.val+1) := by
    intro hm
    have hh := (mem_usedIndices used _ _).mp hm
    rw [hfree] at hh
    exact Bool.noConfusion hh.2
  have hcol := hcomplete.2.2.1.2 target (lt_of_le_of_lt ht bounds.v_len)
  simp only [columnExpected,htargetNot,↓reduceIte,sub_zero] at hcol
  simp only [candidateCost,reducedAt,alloc.vec.Vec.deref,Slice.from_val]
  rw [hrow,hcol]
  ring

/-- The actual returned slack and potentials preserve independent attained
minima over all used candidates, including absent-slack semantics. -/
theorem complete_slack_invariant (cost : Slice (alloc.vec.Vec I64)) (u v : alloc.vec.Vec I128)
    (matched : Slice Usize) (used : Slice Bool) (slack : alloc.vec.Vec (Option I128)) (predecessor : alloc.vec.Vec Usize)
    (amount : I128) (n : Usize) (output : AdjustOutput) (bounds : Bounds u v matched used slack amount n)
    (hcomplete : CompleteAdjustment u v matched used slack amount n output)
    (hinvariant : SlackInvariant cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) matched used
      (usedIndices used (n.val+1)) slack predecessor n) :
    SlackInvariant cost (alloc.vec.Vec.deref output.2.1) (alloc.vec.Vec.deref output.2.2.1) matched used
      (usedIndices used (n.val+1)) output.2.2.2 predecessor n := by
  intro target hp hb hf
  have hs := hcomplete.2.2.2.2 target (lt_of_le_of_lt hb bounds.slack_len)
  have hguard : target < n.val+1 ∧ used.val[target]! = false := ⟨by omega,hf⟩
  simp only [slackExpected,hguard] at hs
  rw [hs]
  apply ((hinvariant target hp hb hf).subtract amount.val).congr
  intro candidate hc
  exact (complete_candidateCost cost u v matched used slack amount n output bounds hcomplete target candidate hb hf hc).symm

end SubtreeProofs.Rust.AssignmentAdjustmentCut

end
