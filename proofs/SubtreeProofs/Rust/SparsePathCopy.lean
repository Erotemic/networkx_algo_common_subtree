module

public import SubtreeProofs.Rust.AssignmentInitialization
import Mathlib.Tactic

/-! # Actual original-index vector copy used by sparse path flipping -/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseSearch

/-- The actual source copy loop preserves every original assignment index
in order and succeeds for every represented slice. -/
theorem copy_indices_spec (values : Slice Usize) :
    sparse_search.copy_indices values ⦃ result => result.val = values.val ⦄ := by
  unfold sparse_search.copy_indices sparse_search.copy_indices_loop
  apply loop.spec_decr_nat (fun state => values.length-state.2.val)
    (fun state => state.2.val ≤ values.length ∧ state.1.val = values.val.take state.2.val)
    _ _ _ ?_ (by simp)
  rintro ⟨result,index⟩ ⟨hIndex,hPrefix⟩
  dsimp only at hIndex hPrefix ⊢
  unfold sparse_search.copy_indices_loop.body
  dsimp only
  split
  · rename_i hlt
    have hi : index.val < values.length := by have hl := Slice.len_val values; scalar_tac
    apply WP.spec_bind (Slice.index_usize_spec values index hi)
    intro value hValue
    have hLen : result.val.length = index.val := by
      rw [hPrefix,List.length_take,Nat.min_eq_left hIndex]
    apply WP.spec_bind (alloc.vec.Vec.push_spec result value (by rw [hLen]; have hl := Slice.len_val values; scalar_tac))
    intro updated hUpdated
    apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by have hl := Slice.len_val values; scalar_tac))
    intro next hNext
    simp only [WP.spec_ok]
    refine ⟨⟨by have hl := Slice.len_val values; scalar_tac,?_⟩,by scalar_tac⟩
    have hn : next.val = index.val+1 := by scalar_tac
    rw [hUpdated,hPrefix,hn,List.take_succ_eq_append_getElem hi,hValue]
  · rename_i hnot
    have he : index.val = values.length := by have hl := Slice.len_val values; scalar_tac
    exact (WP.spec_ok _).mpr (by simpa only [he,List.take_length] using hPrefix)

end SubtreeProofs.Rust.SparseSearch

end
