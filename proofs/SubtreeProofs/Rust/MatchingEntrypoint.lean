module

public import SubtreeProofs.Rust.MatchingSolveBuiltMatrix
public import SubtreeProofs.Rust.MatchingNonpositive
import Mathlib.Tactic

/-!
# Total correctness of the actual public signed partial-matching API

Actual shape and size checks, cost construction, verified assignment, indexed
pair decoding and checked weight conversion compose to a globally maximum
compatible matching with exact input-index witness and weight. Every other
represented input returns its documented shape or size rejection.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.MatchingEntrypoint

open MatchingValidation MatchingCostConstruction MatchingMatrixRepresentation MatchingSolveBuiltMatrix

/-- The represented right-side width is the first supplied row's length;
zero rows represent the empty matrix with width zero. -/
def width (weights : Slice (alloc.vec.Vec (Option I64))) : Usize :=
  match weights.val with
  | [] => 0#usize
  | row::_ => alloc.vec.Vec.len row

def Admissible (weights : Slice (alloc.vec.Vec (Option I64))) : Prop :=
  Rectangular weights (width weights).val ∧ weights.length+(width weights).val ≤ U32.max ∧
    weights.length+(width weights).val < Usize.max

/-- Exact independent maximum witness or documented rejection, including
shape-before-size precedence in the actual wrapper. -/
def ResultSpec (weights : Slice (alloc.vec.Vec (Option I64)))
    (output : core.result.Result matching.PartialMatching matching.MatchingError) : Prop :=
  match output with
  | .Ok result => Admissible weights ∧ CorrectPartial weights (Slice.len weights) (width weights) result
  | .Err error =>
    (error = .NonRectangular ∧ ¬ Rectangular weights (width weights).val) ∨
    (error = .TooLarge ∧ Rectangular weights (width weights).val ∧
      (U32.max < weights.length+(width weights).val ∨ Usize.max ≤ weights.length+(width weights).val))

/-- The actual source expression preceding rectangular validation safely
reads the represented first-row width, or zero for an empty input. -/
theorem width_computation_spec (weights : Slice (alloc.vec.Vec (Option I64))) :
    (if Slice.len weights = 0#usize then ok 0#usize else do
      let row ← Slice.index_usize weights 0#usize
      ok (alloc.vec.Vec.len row)) ⦃ right => right = width weights ⦄ := by
  cases hrows : weights.val with
  | nil =>
    have he : Slice.len weights = 0#usize := by
      apply UScalar.eq_of_val_eq
      simp only [Slice.len_val,Slice.length,hrows,List.length_nil,UScalar.ofNatCore_val_eq]
    simp only [he,↓reduceIte,WP.spec_ok,width,hrows]
  | cons row rest =>
    have hp : 0 < weights.length := by simp only [Slice.length,hrows,List.length_cons]; omega
    have hn : Slice.len weights ≠ 0#usize := by
      intro he
      have hv := congrArg UScalar.val he
      simp only [Slice.len_val,UScalar.ofNatCore_val_eq] at hv
      omega
    simp only [hn,↓reduceIte]
    apply WP.spec_bind (Slice.index_usize_spec weights 0#usize (by scalar_tac))
    intro first hFirst
    simp only [WP.spec_ok,width,hrows]
    have he : first = row := by
      simpa only [hrows,UScalar.ofNatCore_val_eq,List.getElem_cons_zero] using hFirst
    exact congrArg alloc.vec.Vec.len he

theorem checked_dimension_spec (left right : Usize) :
    lift (Usize.checked_add left right) ⦃ output => match output with
      | none => Usize.max < left.val+right.val
      | some dimension => dimension.val = left.val+right.val ⦄ := by
  simp only [lift,WP.spec_ok]
  have h := Usize.checked_add_bv_spec left right
  cases he : Usize.checked_add left right with
  | none => simpa only [he] using h
  | some dimension =>
    simp only [he] at h
    exact h.2.1

theorem usize_max_value : core.num.Usize.MAX.val = Usize.max := by
  simp [core.num.Usize.MAX]

/-- Every represented public call safely terminates with an independent
maximum indexed witness and exact weight, or the prescribed size/shape error.
No optimum, permutation, path or local arithmetic certificate is supplied. -/
theorem max_weight_partial_matching_total_spec (weights : Slice (alloc.vec.Vec (Option I64))) :
    matching.max_weight_partial_matching weights ⦃ output => ResultSpec weights output ⦄ := by
  have hleft := Slice.len_val weights
  unfold matching.max_weight_partial_matching
  apply WP.spec_bind (width_computation_spec weights)
  intro right hRight
  subst right
  apply WP.spec_bind (is_rectangular_spec weights (width weights))
  intro rectangular hRectangular
  cases rectangular with
  | false =>
    have hnot : ¬ Rectangular weights (width weights).val := by
      intro hr
      exact Bool.noConfusion (hRectangular.mpr hr)
    simp only [Bool.false_eq_true,↓reduceIte,WP.spec_ok,ResultSpec]
    exact Or.inl ⟨True.intro,hnot⟩
  | true =>
    have hshape : Rectangular weights (width weights).val := hRectangular.mp rfl
    apply WP.spec_bind (checked_dimension_spec (Slice.len weights) (width weights))
    intro dimensionOption hDimension
    cases dimensionOption with
    | none =>
      simp only [WP.spec_ok,ResultSpec]
      exact Or.inr ⟨True.intro,hshape,Or.inr (by omega)⟩
    | some dimension =>
      have hdimension : dimension.val = (Slice.len weights).val+(width weights).val := hDimension
      apply WP.spec_bind (UScalar.cast_inBounds_spec .Usize core.num.U32.MAX AssignmentEntrypoint.u32_max_fits_usize)
      intro limit hLimit
      have hlimit : limit.val = U32.max := hLimit.trans AssignmentEntrypoint.u32_max_value
      split
      · rename_i hlarge
        have hl : U32.max < weights.length+(width weights).val := by scalar_tac
        simp only [WP.spec_ok,ResultSpec]
        exact Or.inr ⟨True.intro,hshape,Or.inl hl⟩
      · rename_i hnotLarge
        have hsmall : dimension.val ≤ U32.max := by scalar_tac
        split
        · rename_i hmax
          have hv : dimension.val = Usize.max := (congrArg UScalar.val hmax).trans usize_max_value
          simp only [WP.spec_ok,ResultSpec]
          exact Or.inr ⟨True.intro,hshape,Or.inr (by omega)⟩
        · rename_i hnotMax
          have hmax : dimension.val < Usize.max := by
            have hm := usize_max_value
            scalar_tac
          have dims : Dimensions weights (Slice.len weights) (width weights) dimension := ⟨hleft.symm,hdimension,hshape⟩
          apply WP.spec_bind (MatchingNonpositive.has_positive_spec weights)
          intro positive hPositive
          cases positive with
          | true =>
            simp only [↓reduceIte]
            apply WP.spec_bind (cost_matrix_spec weights (Slice.len weights) (width weights) dimension dims)
            intro cost hCost
            apply WP.spec_mono (solve_built_matrix_spec weights (Slice.len weights) (width weights) dimension dims cost hCost hsmall hmax)
            rintro output ⟨result,houtput,hcorrect⟩
            subst output
            exact ⟨⟨hshape,by omega,by omega⟩,hcorrect⟩
          | false =>
            simp only [Bool.false_eq_true,↓reduceIte,WP.spec_ok,ResultSpec]
            exact ⟨⟨hshape,by omega,by omega⟩,
              MatchingNonpositive.empty_correct weights (Slice.len weights) (width weights)
                hleft hshape (hPositive.mp rfl)⟩

/-- Every admitted rectangular optional signed matrix succeeds with an
independently maximum matching, exact input-index witness and exact weight. -/
theorem max_weight_partial_matching_spec (weights : Slice (alloc.vec.Vec (Option I64))) (haccepted : Admissible weights) :
    matching.max_weight_partial_matching weights ⦃ output => ∃ result,
      output = core.result.Result.Ok result ∧ CorrectPartial weights (Slice.len weights) (width weights) result ⦄ := by
  apply WP.spec_mono (max_weight_partial_matching_total_spec weights)
  intro output houtput
  cases output with
  | Ok result => exact ⟨result,rfl,houtput.2⟩
  | Err error =>
    rcases houtput with ⟨_,hshape⟩ | ⟨_,_,hsize⟩
    · exact False.elim (hshape haccepted.1)
    · rcases hsize with hsize | hsize
      · have hs := haccepted.2.1
        omega
      · have hs := haccepted.2.2
        omega

end SubtreeProofs.Rust.MatchingEntrypoint

end
