module

public import SubtreeProofs.Rust.MatchingDeletionRepresentation
public import SubtreeProofs.Rust.MatchingDeletionReuse
import Mathlib.Tactic

/-! # Indexed optimum transport for actual deletion-family branches -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_assignment_core

namespace SubtreeProofs.Rust.MatchingDeletionCorrectness

open MatchingCostSpecification MatchingDecoding MatchingSolveBuiltMatrix MatchingEntrypoint MatchingDeletionRepresentation

/-- Exact indexed-list membership detects exactly the independently matched
right vertices, so copying cannot bypass the vertex-deletion condition. -/
theorem uses_iff_matched (left right removed : Usize) (hr : removed.val < right.val)
    (result : matching.PartialMatching) (pairs : Finset (Fin left.val × Fin right.val))
    (hmem : ∀ pair : Nat × Nat, pair ∈ result.pairs.val.map pairValue ↔
      ∃ concrete ∈ pairs, (concrete.1.val,concrete.2.val) = pair) :
    (∃ pair ∈ result.pairs.val, pair.right = removed) ↔
      (⟨removed.val,hr⟩ : Fin right.val) ∈ WeightedMatching.matchedRight pairs := by
  constructor
  · rintro ⟨pair,hpair,he⟩
    have hv : pairValue pair ∈ result.pairs.val.map pairValue := List.mem_map.mpr ⟨pair,hpair,rfl⟩
    obtain ⟨concrete,hconcrete,hindices⟩ := (hmem (pairValue pair)).mp hv
    apply Finset.mem_image.mpr
    refine ⟨concrete,hconcrete,?_⟩
    apply Fin.ext
    have hs := congrArg Prod.snd hindices
    simpa only [pairValue,he] using hs
  · intro hmatched
    obtain ⟨concrete,hconcrete,he⟩ := Finset.mem_image.mp hmatched
    have hv := (hmem (concrete.1.val,concrete.2.val)).mpr ⟨concrete,hconcrete,rfl⟩
    obtain ⟨pair,hpair,hindices⟩ := List.mem_map.mp hv
    refine ⟨pair,hpair,?_⟩
    apply UScalar.eq_of_val_eq
    have hs := congrArg Prod.snd hindices
    have heval := congrArg Fin.val he
    exact hs.trans heval

/-- An actual correct returned result survives deletion exactly as the
independent mathematical unmatched-vertex theorem prescribes. -/
theorem correct_reuse (left right removed : Usize) (hr : removed.val < right.val)
    (weights : Fin left.val → Fin right.val → Option ℤ) (result : matching.PartialMatching)
    (hcorrect : CorrectFor left right weights result)
    (hunused : ¬ ∃ pair ∈ result.pairs.val, pair.right = removed) :
    CorrectFor left right (WeightedMatching.deleteRight weights ⟨removed.val,hr⟩) result := by
  obtain ⟨pairs,hnodup,hmem,hmaximum,hweight⟩ := hcorrect
  have havoid : (⟨removed.val,hr⟩ : Fin right.val) ∉ WeightedMatching.matchedRight pairs := by
    intro hm
    exact hunused ((uses_iff_matched left right removed hr result pairs hmem).mpr hm)
  refine ⟨pairs,hnodup,hmem,hmaximum.deleteRight _ havoid,?_⟩
  rw [WeightedMatching.weight_deleteRight weights _ pairs havoid]
  exact hweight

/-- Calling the already verified public solver on an actual masked matrix
returns the independent deleted-instance optimum at original input indices. -/
theorem solve_masked_spec (weights : Slice (alloc.vec.Vec (Option I64))) (removed : Usize)
    (masked : alloc.vec.Vec (alloc.vec.Vec (Option I64))) (h : Masked weights removed masked)
    (ha : Admissible weights) (hr : removed.val < (width weights).val) :
    matching.max_weight_partial_matching (alloc.vec.Vec.deref masked) ⦃ output => ∃ result,
      output = core.result.Result.Ok result ∧
      CorrectFor (Slice.len weights) (width weights)
        (WeightedMatching.deleteRight (weightsModel weights (Slice.len weights).val (width weights).val) ⟨removed.val,hr⟩) result ⦄ := by
  apply WP.spec_mono (max_weight_partial_matching_spec (alloc.vec.Vec.deref masked)
    (masked_admissible weights removed masked h ha))
  rintro output ⟨result,houtput,hcorrect⟩
  refine ⟨result,houtput,?_⟩
  rw [masked_len weights removed masked h,masked_width weights removed masked h] at hcorrect
  change CorrectFor (Slice.len weights) (width weights)
    (weightsModel (alloc.vec.Vec.deref masked) (Slice.len weights).val (width weights).val) result at hcorrect
  rw [masked_model weights removed masked h (Slice.len weights) (width weights) (by simp only [Slice.len_val]; omega) ha.1 hr] at hcorrect
  exact hcorrect

end SubtreeProofs.Rust.MatchingDeletionCorrectness

end
