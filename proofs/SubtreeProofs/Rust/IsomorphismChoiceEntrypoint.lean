module

public import SubtreeProofs.Rust.IsomorphismChoiceEmission
import Mathlib.Tactic

/-! # Actual production ordered-isomorphism choice materialization -/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_ordered_core.isomorphism_choices

namespace SubtreeProofs.Rust.IsomorphismChoices

theorem emission_loop_spec (choices : Slice IsomorphismChoice) (hValid : ValidArena choices)
    (targetLeft targetRight : List U32) (hLeftBound : targetLeft.length ≤ Usize.max)
    (hRightBound : targetRight.length ≤ Usize.max)
    (pending : alloc.vec.Vec Visit) (left right : alloc.vec.Vec U32) (length : Usize)
    (h : EmissionInvariant choices targetLeft targetRight (pending,left,right,length)) :
    reconstruct_isomorphism_choices_loop choices pending left right length ⦃ output =>
      EmissionPost targetLeft targetRight output ⦄ := by
  unfold reconstruct_isomorphism_choices_loop
  apply loop.spec_decr_nat (fun state => (remaining choices state).length)
    (EmissionInvariant choices targetLeft targetRight) (EmissionPost targetLeft targetRight)
    _ (pending,left,right,length) ?_ h
  rintro ⟨pending1,left1,right1,length1⟩ h1
  apply WP.spec_mono (emission_body_spec choices hValid targetLeft targetRight hLeftBound hRightBound
    pending1 left1 right1 length1 h1)
  intro result hResult
  cases result <;> exact hResult

/-- The actual production helper terminates and emits exactly the independent
arena forest's original token coordinates in both inputs. The assumptions are
earlier-child references, a valid root and representable output size; no loop
success, supplied output, score or optimality certificate is assumed. -/
theorem reconstruct_isomorphism_choices_spec (choices : Slice IsomorphismChoice)
    (root : Option Usize) (hValid : ValidArena choices)
    (hRoot : ∀ index, root = some index → index.val < choices.length)
    (hSize : (tokens (optionalTree choices root)).length ≤ Usize.max) :
    reconstruct_isomorphism_choices choices root ⦃ output =>
      EmissionPost ((tokens (optionalTree choices root)).map Prod.fst)
        ((tokens (optionalTree choices root)).map Prod.snd) output ⦄ := by
  unfold reconstruct_isomorphism_choices
  cases root with
  | none =>
    simp only [bind_ok]
    apply emission_loop_spec choices hValid _ _ (by simp [optionalTree,tokens])
      (by simp [optionalTree,tokens])
    constructor
    · simp [alloc.vec.Vec.new,alloc.vec.Vec.length]
    · simp [ValidStack,active,alloc.vec.Vec.new]
    · simp [remaining,active,alloc.vec.Vec.new,optionalTree,tokens]
    · simp [remaining,active,alloc.vec.Vec.new,optionalTree,tokens]
  | some index =>
    apply WP.spec_bind (alloc.vec.Vec.push_spec (alloc.vec.Vec.new Visit) (Visit.Pair index) (by
      simp only [alloc.vec.Vec.new,alloc.vec.Vec.from_val,List.length_nil]
      scalar_tac))
    intro pending hPending
    apply emission_loop_spec choices hValid _ _ (by simpa only [List.length_map] using hSize)
      (by simpa only [List.length_map] using hSize)
    have hActive : active pending (alloc.vec.Vec.len pending) = [Visit.Pair index] := by
      simp only [active,alloc.vec.Vec.len_val,alloc.vec.Vec.length,List.take_length,hPending,
        alloc.vec.Vec.new,alloc.vec.Vec.from_val,List.nil_append]
    constructor
    · exact le_of_eq (alloc.vec.Vec.len_val pending)
    · rw [hActive]
      simpa [ValidStack,ValidVisit] using hRoot index rfl
    · simp [remaining,hActive,stackTokens,visitTokens,optionalTree,alloc.vec.Vec.new]
    · simp [remaining,hActive,stackTokens,visitTokens,optionalTree,alloc.vec.Vec.new]

end SubtreeProofs.Rust.IsomorphismChoices

end
