module

public import SubtreeProofs.Rust.SparseDeletionProjection
import Mathlib.Tactic

/-! # Actual sparse-deletion original-column readback -/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseDeletion

/-- The actual checked exporter terminates with original columns in row order
when every compact column selects an existing surviving original vertex. -/
theorem original_columns_loop_spec (columns vertices : Slice Usize)
    (hBounds : ∀ column ∈ columns.val, column.val < vertices.length) :
    sparse_deletion.original_columns_loop columns vertices (alloc.vec.Vec.new Usize) 0#usize none ⦃ result =>
      result.2 = none ∧ result.1.val = columns.val.map (fun column => vertices.val[column.val]!) ⦄ := by
  unfold sparse_deletion.original_columns_loop
  apply loop.spec_decr_nat (fun state => columns.length-state.2.1.val)
    (fun state => state.2.2 = none ∧ state.2.1.val ≤ columns.length ∧
      state.1.val = (columns.val.take state.2.1.val).map (fun column => vertices.val[column.val]!))
    _ _ _ ?_ (by simp)
  rintro ⟨result,index,failure⟩ ⟨rfl,hIndex,hPrefix⟩
  dsimp only at hIndex hPrefix ⊢
  unfold sparse_deletion.original_columns_loop.body
  dsimp only
  split
  · rename_i hlt
    have hLen := Slice.len_val columns
    have hi : index.val < columns.length := by scalar_tac
    simp only [core.option.Option.is_none]
    apply WP.spec_bind (Slice.index_usize_spec columns index hi)
    intro column hColumn
    have hm : column ∈ columns.val := by rw [hColumn]; exact List.getElem_mem hi
    have hc := hBounds column hm
    have hNoError : ¬ column ≥ Slice.len vertices := by have hl := Slice.len_val vertices; scalar_tac
    simp only [hNoError,↓reduceIte,Std.bind_assoc]
    apply WP.spec_bind (Slice.index_usize_spec vertices column hc)
    intro vertex hVertex
    have hResultLength : result.val.length = index.val := by
      rw [hPrefix,List.length_map,List.length_take,Nat.min_eq_left hIndex]
    apply WP.spec_bind (alloc.vec.Vec.push_spec result vertex (by rw [hResultLength]; scalar_tac))
    intro updated hUpdated
    simp only [bind_ok,uncurry_apply_pair]
    apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    intro next hNext
    simp only [WP.spec_ok]
    refine ⟨⟨True.intro,by scalar_tac,?_⟩,by scalar_tac⟩
    have hn : next.val = index.val+1 := by scalar_tac
    rw [hUpdated,hPrefix,hn,List.take_succ_eq_append_getElem hi,List.map_append,List.map_singleton,← hColumn]
    congr 2
    simpa only [getElem!_pos vertices.val column.val hc] using hVertex
  · rename_i hnot
    have he : index.val = columns.length := by have hl := Slice.len_val columns; scalar_tac
    exact (WP.spec_ok _).mpr ⟨rfl,by simpa only [he,List.take_length] using hPrefix⟩

/-- Source readback succeeds without a compression/permutation assumption;
its sole precondition is the actual checked original-vertex lookup bound. -/
theorem original_columns_spec (columns vertices : Slice Usize)
    (hBounds : ∀ column ∈ columns.val, column.val < vertices.length) :
    sparse_deletion.original_columns columns vertices ⦃ result => ∃ output,
      result = core.result.Result.Ok output ∧
      output.val = columns.val.map (fun column => vertices.val[column.val]!) ⦄ := by
  unfold sparse_deletion.original_columns
  apply WP.spec_bind (original_columns_loop_spec columns vertices hBounds)
  rintro ⟨output,failure⟩ ⟨rfl,hOutput⟩
  exact (WP.spec_ok _).mpr ⟨output,rfl,hOutput⟩

end SubtreeProofs.Rust.SparseDeletion

end
