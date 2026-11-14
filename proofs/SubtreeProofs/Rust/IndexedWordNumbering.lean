module

public import SubtreeProofs.Rust.IndexedWordRepresentation
import Mathlib.Tactic

/-! # Actual checked preorder numbering: exact original indices and counter -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.IndexedOrderedSolver

open OrderedSolver

/-- The source numbering safely assigns consecutive original pair indices,
preserves the input shape and returns precisely its first unused counter. -/
theorem number_word_refines (word : BalancedWord) (next : U32)
    (hbound : next.val + (toDyck word).semilength < 2^32) :
    ∃ result : indexed.NumberedWord,
      indexed.number_word word next = .ok (some result) ∧
      Paper2004.IndexedWord.erase (model result.word) = toDyck word ∧
      Paper2004.IndexedWord.indices (model result.word) = List.range' next.val (toDyck word).semilength ∧
      result.next.val = next.val + (toDyck word).semilength := by
  induction word generalizing next with
  | Empty =>
    refine ⟨⟨.Empty,next⟩,?_,?_,?_,?_⟩
    · rw [indexed.number_word]
    · rfl
    · rfl
    · simp only [toDyck,DyckWord.semilength_zero,Nat.add_zero]
  | Pair head tail ihHead ihTail =>
    have hs := hbound
    simp only [toDyck,DyckWord.semilength_add,DyckWord.semilength_nest] at hs
    obtain ⟨following,hFollowing,hFollowingVal⟩ := checked_add_success next 1#u32 (by scalar_tac)
    have hf : following.val = next.val+1 := by simpa using hFollowingVal
    obtain ⟨inside,hInside,hInsideShape,hInsideIndices,hInsideEnd⟩ := ihHead following (by omega)
    obtain ⟨outside,hOutside,hOutsideShape,hOutsideIndices,hOutsideEnd⟩ := ihTail inside.next (by omega)
    refine ⟨⟨.Pair next inside.word outside.word,outside.next⟩,?_,?_,?_,?_⟩
    · rw [indexed.number_word]
      simp only [lift,hFollowing,bind_ok,hInside,hOutside]
    · simp only [model,Paper2004.IndexedWord.erase,toDyck,hInsideShape,hOutsideShape]
    · simp only [model,Paper2004.IndexedWord.indices,hInsideIndices,hOutsideIndices,hInsideEnd,hf]
      rw [List.range'_append_1]
      simp only [toDyck,DyckWord.semilength_add,DyckWord.semilength_nest]
      have hc : (toDyck head).semilength+1+(toDyck tail).semilength =
          (toDyck head).semilength+(toDyck tail).semilength+1 := by omega
      rw [hc,List.range'_succ]
    · simp only [toDyck,DyckWord.semilength_add,DyckWord.semilength_nest]
      omega

end SubtreeProofs.Rust.IndexedOrderedSolver

end
