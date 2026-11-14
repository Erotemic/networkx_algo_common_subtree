module

public import SubtreeProofs.Rust.TokenParserRepresentation
public import SubtreeProofs.Paper2004.CanonicalTokenPositions
import Mathlib.Tactic

/-! # Actual retained-pair emitter preserves the original token coordinates -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.TokenMatching

open IndexedOrderedSolver TokenParser Paper2004.IndexedWord

/-- Concrete token-index vector interpreted without discarding order or duplicates. -/
def tokenView (output : alloc.vec.Vec Usize) : List Nat := output.val.map UScalar.val

@[simp] theorem tokenView_length (output : alloc.vec.Vec Usize) :
    (tokenView output).length = output.length := by simp only [tokenView,List.length_map,alloc.vec.Vec.length]

/-- The actual emitter appends both original endpoints of every retained pair.
The bounds concern the actual coordinate slice and output capacity; all source
casts, reads and recursive pushes are discharged from them. -/
theorem emit_tokens_spec (word : indexed.IndexedWord) (coordinates : Slice tokens.PairPositions)
    (output : alloc.vec.Vec Usize)
    (hi : ∀ index ∈ indices (model word), index < coordinates.length)
    (hb : output.length+2*(model word).numNodes ≤ Usize.max) :
    token_matching.emit_tokens word coordinates output ⦃ result => ∃ emitted,
      result = core.result.Result.Ok emitted ∧
      tokenView emitted = tokenView output ++
        tokenIndices (fun index => (coordinates.val.map positionValue)[index]!) (model word) ⦄ := by
  induction word generalizing output with
  | Empty =>
    rw [token_matching.emit_tokens]
    simp only [WP.spec_ok,model,tokenIndices,List.append_nil]
    exact ⟨output,rfl,rfl⟩
  | Pair index head tail ihHead ihTail =>
    have hid : index.val < coordinates.length := hi index.val (by simp only [model,indices,List.mem_cons]; exact Or.inl True.intro)
    have hhead : ∀ i ∈ indices (model head), i < coordinates.length := by
      intro i hm
      exact hi i (by simp only [model,indices,List.mem_cons,List.mem_append]; exact Or.inr (Or.inl hm))
    have htail : ∀ i ∈ indices (model tail), i < coordinates.length := by
      intro i hm
      exact hi i (by simp only [model,indices,List.mem_cons,List.mem_append]; exact Or.inr (Or.inr hm))
    have hcount : (model (.Pair index head tail)).numNodes = (model head).numNodes+(model tail).numNodes+1 := rfl
    
    have hcast : index.val ≤ UScalar.max .Usize := by
      have hu := u32_max_fits_usize
      have hv := u32_max_value
      scalar_tac
    unfold token_matching.emit_tokens
    apply WP.spec_bind (UScalar.cast_inBounds_spec .Usize index hcast)
    intro pair hPair
    have hlen := Slice.len_val coordinates
    have hsmall : ¬ pair ≥ Slice.len coordinates := by scalar_tac
    simp only [hsmall,↓reduceIte]
    apply WP.spec_bind (Slice.index_usize_spec coordinates pair (by omega))
    intro position hPosition
    have hposition : (coordinates.val.map positionValue)[index.val]! = positionValue position := by
      rw [getElem!_pos (coordinates.val.map positionValue) index.val (by simpa only [List.length_map] using hid)]
      simp only [List.getElem_map]
      rw [hPosition]
      congr 2
      exact hPair.symm
    apply WP.spec_bind (alloc.vec.Vec.push_spec output position.«open» (by change output.length < Usize.max; rw [hcount] at hb; omega))
    intro inside hInside
    have hinsideLen : inside.length = output.length+1 := by
      simp only [alloc.vec.Vec.length,hInside,List.length_append,List.length_singleton]
    apply WP.spec_bind (ihHead inside hhead (by rw [hcount] at hb; omega))
    rintro headResult ⟨headOutput,hHeadResult,hHead⟩
    subst headResult
    have hheadLen : headOutput.length = inside.length+2*(model head).numNodes := by
      have hh := congrArg List.length hHead
      simpa only [tokenView_length,List.length_append,tokenIndices_length] using hh
    apply WP.spec_bind (alloc.vec.Vec.push_spec headOutput position.close (by change headOutput.length < Usize.max; rw [hcount] at hb; omega))
    intro outside hOutside
    have houtsideLen : outside.length = headOutput.length+1 := by
      simp only [alloc.vec.Vec.length,hOutside,List.length_append,List.length_singleton]
    apply WP.spec_mono (ihTail outside htail (by rw [hcount] at hb; omega))
    rintro result ⟨emitted,hResult,hEmitted⟩
    refine ⟨emitted,hResult,?_⟩
    rw [hEmitted]
    simp only [tokenView,hOutside,List.map_append,List.map_cons,List.map_nil]
    change (tokenView headOutput ++ [position.close.val]) ++ _ = _
    rw [hHead]
    simp only [tokenView,hInside,List.map_append,List.map_cons,List.map_nil,model,tokenIndices,hposition,positionValue,
      List.append_assoc,List.cons_append,List.nil_append]

end SubtreeProofs.Rust.TokenMatching

end
