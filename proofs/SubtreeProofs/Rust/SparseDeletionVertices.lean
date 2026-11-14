module

public import SubtreeProofs.Rust.SparseDeletionIndices
public import SubtreeProofs.Shared.AssignmentSurvivingIndices
import Mathlib.Tactic

/-! # Actual increasing survivor-coordinate enumeration for sparse deletion -/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseDeletion

abbrev survivingIndices := AssignmentVertexDeletion.survivingIndices

theorem survivingIndices_succ (extent removed : Nat) :
    survivingIndices (extent+1) removed =
      if extent = removed then survivingIndices extent removed else survivingIndices extent removed ++ [extent] :=
  AssignmentVertexDeletion.survivingIndices_succ extent removed

/-- Every represented source loop returns the original indices in increasing
order with exactly the removed index omitted. This includes an out-of-range
removed value, where the private builder simply retains every vertex. -/
theorem surviving_vertices_spec (n removed : Usize) :
    sparse_deletion.surviving_vertices n removed ⦃ vertices => vertices.val.map UScalar.val = survivingIndices n.val removed.val ⦄ := by
  unfold sparse_deletion.surviving_vertices sparse_deletion.surviving_vertices_loop
  apply loop.spec_decr_nat (fun state => n.val-state.2.val)
    (fun state => state.2.val ≤ n.val ∧ state.1.length ≤ state.2.val ∧
      state.1.val.map UScalar.val = survivingIndices state.2.val removed.val)
    _ _ _ ?_ (by simp [survivingIndices,AssignmentVertexDeletion.survivingIndices])
  rintro ⟨vertices,vertex⟩ ⟨hCursor,hLength,hPrefix⟩
  dsimp only at hCursor hLength hPrefix ⊢
  unfold sparse_deletion.surviving_vertices_loop.body
  split
  · rename_i hlt
    have hb : vertex.val < n.val := hlt
    by_cases he : vertex = removed
    · have hFlag : (vertex != removed) = false := by rw [he]; exact bne_self_eq_false _
      simp only [hFlag,Bool.false_eq_true,↓reduceIte,bind_ok]
      apply WP.spec_bind (Usize.add_spec (x := vertex) (y := 1#usize) (by scalar_tac))
      intro next hNext
      simp only [WP.spec_ok]
      refine ⟨⟨by scalar_tac,by scalar_tac,?_⟩,by scalar_tac⟩
      have hn : next.val = vertex.val+1 := by scalar_tac
      rw [hn,survivingIndices_succ,ite_eq_left (congrArg UScalar.val he)]
      exact hPrefix
    · have hNe : vertex.val ≠ removed.val := fun hh => he (UScalar.eq_of_val_eq hh)
      have hFlag : (vertex != removed) = true := bne_iff_ne.mpr he
      simp only [hFlag,↓reduceIte]
      apply WP.spec_bind (alloc.vec.Vec.push_spec vertices vertex (by change vertices.length < Usize.max; scalar_tac))
      intro updated hUpdated
      apply WP.spec_bind (Usize.add_spec (x := vertex) (y := 1#usize) (by scalar_tac))
      intro next hNext
      simp only [WP.spec_ok]
      refine ⟨⟨by scalar_tac,?_,?_⟩,by scalar_tac⟩
      · have hLen : updated.length = vertices.length+1 := by simp only [alloc.vec.Vec.length,hUpdated,List.length_append,List.length_singleton]
        scalar_tac
      · have hn : next.val = vertex.val+1 := by scalar_tac
        rw [hUpdated,List.map_append,hPrefix,hn,survivingIndices_succ,ite_eq_right hNe]
        rfl
  · rename_i hnot
    have he : vertex.val = n.val := by scalar_tac
    exact (WP.spec_ok _).mpr (by simpa only [he] using hPrefix)

end SubtreeProofs.Rust.SparseDeletion

end
