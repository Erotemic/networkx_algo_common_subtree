module

public import SubtreeProofs.Rust.MatchingDeletionInvariant
import Mathlib.Tactic

/-! # Total correctness of the actual exact matching deletion-family API -/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.MatchingDeletionEntrypoint

open MatchingCostSpecification MatchingSolveBuiltMatrix MatchingEntrypoint MatchingDeletionReuse
open MatchingDeletionMask MatchingDeletionRepresentation MatchingDeletionCorrectness MatchingDeletionInvariant

/-- Complete actual family loop: every deleted instance is independently
maximum with exact original indices and weight, and unused deletions copy the
original result exactly. All possible internal errors are ruled out. -/
theorem deletion_loop_spec (weights : Slice (alloc.vec.Vec (Option I64))) (original : matching.PartialMatching)
    (ha : Admissible weights) (hOriginal : CorrectPartial weights (Slice.len weights) (width weights) original) :
    deletion.max_weight_matching_deletions_loop weights original (width weights) (alloc.vec.Vec.new matching.PartialMatching) 0#usize
      ⦃ output => ∃ family, output = core.result.Result.Ok family ∧ CorrectFamily weights family ⦄ := by
  unfold deletion.max_weight_matching_deletions_loop
  apply loop.spec_decr_nat
    (fun (state : alloc.vec.Vec matching.PartialMatching × Usize) => (width weights).val-state.2.val)
    (fun (state : alloc.vec.Vec matching.PartialMatching × Usize) => Invariant weights original state.1 state.2)
    (fun output => ∃ family, output = core.result.Result.Ok family ∧ CorrectFamily weights family)
    _ (alloc.vec.Vec.new matching.PartialMatching,0#usize) ?_ ?_
  · rintro ⟨results,removed⟩ h
    dsimp only at h ⊢
    have hb := h.bound
    have hlen := h.length
    unfold deletion.max_weight_matching_deletions_loop.body
    split
    · rename_i hr
      have hp : removed.val < (width weights).val := by scalar_tac
      apply WP.spec_bind (uses_right_spec (alloc.vec.Vec.deref original.pairs) removed)
      intro used hUsed
      have hdetect : used = true ↔ ∃ pair ∈ original.pairs.val, pair.right = removed := by
        simpa only [alloc.vec.Vec.deref,Slice.from_val] using hUsed
      cases used with
      | true =>
        simp only [↓reduceIte]
        apply WP.spec_bind (mask_right_spec weights removed)
        intro masked hMasked
        apply WP.spec_bind (solve_masked_spec weights removed masked hMasked ha hp)
        rintro solution ⟨result,hSolution,hCorrect⟩
        subst solution
        have hcopy : Unused original removed.val → result = original := by
          intro hunused
          obtain ⟨pair,hpair,he⟩ := hdetect.mp rfl
          exact False.elim ((hunused pair hpair) (congrArg UScalar.val he))
        apply WP.spec_bind (alloc.vec.Vec.push_spec results result (by scalar_tac))
        intro nextResults hNextResults
        apply WP.spec_bind (Usize.add_spec (x := removed) (y := 1#usize) (by scalar_tac))
        intro next hNext
        have hn : next.val = removed.val+1 := by simpa using hNext
        simp only [WP.spec_ok]
        exact ⟨append_invariant weights original results nextResults removed next result h hp hNextResults hn hCorrect hcopy,by omega⟩
      | false =>
        simp only [Bool.false_eq_true,↓reduceIte]
        have hunused : ¬ ∃ pair ∈ original.pairs.val, pair.right = removed := by
          intro he
          exact Bool.noConfusion (hdetect.mpr he)
        have hCorrect := correct_reuse (Slice.len weights) (width weights) removed hp
          (weightsModel weights (Slice.len weights).val (width weights).val) original hOriginal hunused
        apply WP.spec_bind (copy_matching_spec original)
        intro result hResult
        subst result
        apply WP.spec_bind (alloc.vec.Vec.push_spec results original (by scalar_tac))
        intro nextResults hNextResults
        apply WP.spec_bind (Usize.add_spec (x := removed) (y := 1#usize) (by scalar_tac))
        intro next hNext
        have hn : next.val = removed.val+1 := by simpa using hNext
        simp only [WP.spec_ok]
        exact ⟨append_invariant weights original results nextResults removed next original h hp hNextResults hn hCorrect (fun _ => rfl),by omega⟩
    · rename_i hr
      have he : removed = width weights := UScalar.eq_of_val_eq (by scalar_tac)
      simp only [WP.spec_ok]
      refine ⟨⟨original,results⟩,rfl,hOriginal,?_⟩
      simpa only [he] using h
  · refine ⟨by simp,by simp,?_,?_⟩
    · intro column hc
      simp only [UScalar.ofNatCore_val_eq] at hc
      omega
    · intro column hc
      simp only [UScalar.ofNatCore_val_eq] at hc
      omega

def ResultSpec (weights : Slice (alloc.vec.Vec (Option I64)))
    (output : core.result.Result deletion.DeletionFamily matching.MatchingError) : Prop :=
  match output with
  | .Ok family => Admissible weights ∧ CorrectFamily weights family
  | .Err error => MatchingEntrypoint.ResultSpec weights (.Err error)

/-- Every represented call returns the exact original/deletion family or the
prescribed original shape/size rejection. No path, optimum, arithmetic or
per-deletion result certificate is supplied as an endpoint premise. -/
theorem max_weight_matching_deletions_total_spec (weights : Slice (alloc.vec.Vec (Option I64))) :
    deletion.max_weight_matching_deletions weights ⦃ output => ResultSpec weights output ⦄ := by
  unfold deletion.max_weight_matching_deletions
  apply WP.spec_bind (max_weight_partial_matching_total_spec weights)
  intro originalOutput hOriginal
  cases originalOutput with
  | Err error =>
    simp only [WP.spec_ok,ResultSpec]
    exact hOriginal
  | Ok original =>
    obtain ⟨ha,hcorrect⟩ := hOriginal
    apply WP.spec_bind (width_computation_spec weights)
    intro right hRight
    subst right
    apply WP.spec_mono (deletion_loop_spec weights original ha hcorrect)
    rintro output ⟨family,houtput,hfamily⟩
    subst output
    exact ⟨ha,hfamily⟩

/-- Every admitted input succeeds with all independently maximum indexed
witnesses and exact scores; unused deletions reproduce the original result. -/
theorem max_weight_matching_deletions_spec (weights : Slice (alloc.vec.Vec (Option I64))) (ha : Admissible weights) :
    deletion.max_weight_matching_deletions weights ⦃ output => ∃ family,
      output = core.result.Result.Ok family ∧ CorrectFamily weights family ⦄ := by
  apply WP.spec_mono (max_weight_matching_deletions_total_spec weights)
  intro output hOutput
  cases output with
  | Ok family => exact ⟨family,rfl,hOutput.2⟩
  | Err error =>
    rcases hOutput with ⟨_,hshape⟩ | ⟨_,_,hsize⟩
    · exact False.elim (hshape ha.1)
    · rcases hsize with hs | hs
      · have hb := ha.2.1
        omega
      · have hb := ha.2.2
        omega

end SubtreeProofs.Rust.MatchingDeletionEntrypoint

end
