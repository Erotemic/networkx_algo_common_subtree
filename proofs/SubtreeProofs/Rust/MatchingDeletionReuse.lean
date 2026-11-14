module

public import SubtreeProofs.Rust.MatchingEntrypoint
public import SubtreeProofs.Shared.MatchingDeletion
import Mathlib.Tactic

/-! # Actual unmatched-column detection and result copying for deletion reuse -/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.MatchingDeletionReuse

instance : Inhabited matching.MatchedPair := ⟨⟨0#usize,0#usize⟩⟩

/-- The actual early-return loop detects precisely an existing right endpoint. -/
theorem uses_right_loop_spec (pairs : Slice matching.MatchedPair) (right index : Usize)
    (hi : index.val ≤ pairs.length) (hprefix : ∀ position < index.val, (pairs.val[position]!).right ≠ right) :
    deletion.uses_right_loop pairs right index ⦃ result => result = true ↔ ∃ pair ∈ pairs.val, pair.right = right ⦄ := by
  unfold deletion.uses_right_loop
  apply loop.spec_decr_nat (fun current => pairs.length-current.val)
    (fun current => current.val ≤ pairs.length ∧ ∀ position < current.val, (pairs.val[position]!).right ≠ right)
    (fun result => result = true ↔ ∃ pair ∈ pairs.val, pair.right = right) _ index ?_ ⟨hi,hprefix⟩
  intro current hinv
  rcases hinv with ⟨hb,hseen⟩
  have hlen := Slice.len_val pairs
  unfold deletion.uses_right_loop.body
  dsimp only
  split
  · rename_i hr
    have hp : current.val < pairs.length := by scalar_tac
    apply WP.spec_bind (Slice.index_usize_spec pairs current hp)
    intro pair hPair
    have hpair : pair = pairs.val[current.val]! := by
      simpa only [getElem!_pos pairs.val current.val hp] using hPair
    split
    · rename_i hsame
      simp only [WP.spec_ok,eq_self,true_iff]
      refine ⟨pair,?_,hsame⟩
      rw [hPair]
      exact List.getElem_mem hp
    · rename_i hother
      apply WP.spec_bind (Usize.add_spec (x := current) (y := 1#usize) (by scalar_tac))
      intro next hNext
      have hn : next.val = current.val+1 := by simpa using hNext
      simp only [WP.spec_ok]
      refine ⟨⟨by omega,?_⟩,by omega⟩
      intro position hposition
      by_cases he : position = current.val
      · subst position
        simpa only [hpair] using hother
      · exact hseen position (by omega)
  · rename_i hr
    simp only [WP.spec_ok,Bool.false_eq_true,false_iff]
    rintro ⟨pair,hmem,he⟩
    obtain ⟨position,hposition,hpair⟩ := List.mem_iff_getElem.mp hmem
    have hs := hseen position (by scalar_tac)
    rw [getElem!_pos pairs.val position hposition,hpair] at hs
    exact hs he

theorem uses_right_spec (pairs : Slice matching.MatchedPair) (right : Usize) :
    deletion.uses_right pairs right ⦃ result => result = true ↔ ∃ pair ∈ pairs.val, pair.right = right ⦄ := by
  exact uses_right_loop_spec pairs right 0#usize (by simp) (by simp)

/-- Actual owned output copying preserves every pair and the exact weight. -/
theorem copy_matching_spec (original : matching.PartialMatching) :
    deletion.copy_matching original ⦃ result => result = original ⦄ := by
  unfold deletion.copy_matching
  have hloop : deletion.copy_matching_loop original (alloc.vec.Vec.new matching.MatchedPair) 0#usize ⦃ output =>
      output.1 = original.weight ∧ output.2.val = original.pairs.val ⦄ := by
    unfold deletion.copy_matching_loop
    apply loop.spec_decr_nat
      (fun (state : alloc.vec.Vec matching.MatchedPair × Usize) => original.pairs.length-state.2.val)
      (fun (state : alloc.vec.Vec matching.MatchedPair × Usize) => state.2.val ≤ original.pairs.length ∧
        state.1.val = original.pairs.val.take state.2.val)
      (fun (output : I128 × alloc.vec.Vec matching.MatchedPair) => output.1 = original.weight ∧ output.2.val = original.pairs.val)
      _ _ ?_ (by simp)
    rintro ⟨pairs,index⟩ ⟨hindex,hprefix⟩
    dsimp only at hindex hprefix ⊢
    have hlen := alloc.vec.Vec.len_val original.pairs
    unfold deletion.copy_matching_loop.body
    dsimp only
    split
    · rename_i hi
      have hp : index.val < original.pairs.length := by scalar_tac
      have hc : pairs.length = index.val := by
        have he := congrArg List.length hprefix
        simpa only [List.length_take,Nat.min_eq_left hindex] using he
      simp only [alloc.vec.Vec.index_slice_index]
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec original.pairs index hp)
      intro pair hPair
      apply WP.spec_bind (alloc.vec.Vec.push_spec pairs pair (by scalar_tac))
      intro nextPairs hNextPairs
      apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      intro next hNext
      have hn : next.val = index.val+1 := by simpa using hNext
      simp only [WP.spec_ok]
      refine ⟨⟨by omega,?_⟩,by omega⟩
      rw [hNextPairs,hprefix,hn,List.take_succ_eq_append_getElem hp]
      exact congrArg (fun entry => original.pairs.val.take index.val ++ [entry]) hPair
    · rename_i hi
      have he : index.val = original.pairs.length := by scalar_tac
      simp only [WP.spec_ok,eq_self,true_and]
      simpa only [he,List.take_length] using hprefix
  apply WP.spec_bind hloop
  rintro ⟨weight,pairs⟩ ⟨hweight,hpairs⟩
  have hp : pairs = original.pairs := by
    apply alloc.vec.Vec.ext
    exact hpairs
  cases original
  simp_all

end SubtreeProofs.Rust.MatchingDeletionReuse

end
