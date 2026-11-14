module

public import SubtreeProofs.Rust.SparsePathFlipLoop
import Mathlib.Tactic

/-! # Actual public path flip refines a finite original-coordinate permutation -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseSearch

/-- Actual checked Rust path flipping succeeds from a represented completed
permutation and positive decreasing predecessor ranks. The finite simple path
is constructed internally. Every returned index equals the canonical cyclic
augmentation permutation at its original row coordinate. -/
theorem flip_sparse_path_spec (dimension : Nat) (completed predecessor discovery : Slice Usize) (n rootIndex target : Usize)
    (assignment : Equiv.Perm (Fin dimension)) (root : Fin dimension) (parent : Fin dimension → Fin dimension) (rank : Fin dimension → Nat)
    (input : FlipInput dimension completed predecessor discovery n rootIndex assignment root parent rank)
    (hSize : dimension ≤ U32.max) (hTarget : target.val = (assignment root).val) (hStart : 0 < rank (assignment root)) :
    sparse_search.flip_sparse_path completed predecessor discovery rootIndex target ⦃ result => ∃ rest output,
      result = core.result.Result.Ok output ∧
      Assignment.PredecessorTrace assignment parent root (assignment root) (assignment root::rest) ∧ (assignment root::rest).Nodup ∧
      (∀ column ∈ assignment root::rest, 0 < rank column) ∧ output.length = dimension ∧
      ∀ row : Fin dimension, output.val[row.val]!.val = (Assignment.augmentTrace assignment (assignment root::rest) row).val ⦄ := by
  obtain ⟨rest,hTrace,hNodup,hBounds⟩ := Assignment.exists_ranked_predecessor_trace assignment parent root rank input.ranked (assignment root) hStart
  have hPositive : ∀ column ∈ assignment root::rest, 0 < rank column := fun column hc => (hBounds column hc).1
  have hn : Slice.len completed = n := UScalar.eq_of_val_eq (by
    rw [Slice.len_val,input.completed_length,input.dimension_eq])
  have hp : Slice.len predecessor = n := UScalar.eq_of_val_eq (by
    rw [Slice.len_val,input.predecessor_length,input.dimension_eq])
  have hd : Slice.len discovery = n := UScalar.eq_of_val_eq (by
    rw [Slice.len_val,input.discovery_length,input.dimension_eq])
  unfold sparse_search.flip_sparse_path
  simp only [hn,hp,hd,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
  apply WP.spec_bind (UScalar.cast_inBounds_spec .Usize core.num.U32.MAX AssignmentEntrypoint.u32_max_fits_usize)
  intro limit hLimit
  have hLimitVal : limit.val = U32.max := hLimit.trans AssignmentEntrypoint.u32_max_value
  have hNBound : ¬ n > limit := by have he := input.dimension_eq; scalar_tac
  have hRoot : rootIndex.val < dimension := by rw [input.root_eq]; exact root.isLt
  have hRootBound : ¬ rootIndex ≥ n := by have he := input.dimension_eq; scalar_tac
  have hTargetBound : ¬ target ≥ n := by have he := input.dimension_eq; have hb := (assignment root).isLt; scalar_tac
  simp only [hNBound,hRootBound,hTargetBound,↓reduceIte]
  apply WP.spec_bind (Slice.index_usize_spec completed rootIndex (by rw [input.completed_length]; exact hRoot))
  intro initialTarget hRead
  have hReadEq : initialTarget = completed.val[rootIndex.val]! := by
    simpa only [getElem!_pos completed.val rootIndex.val (by change rootIndex.val < completed.length; rw [input.completed_length]; exact hRoot)] using hRead
  have hTargetEq : initialTarget = target := by
    apply UScalar.eq_of_val_eq
    rw [hReadEq,input.root_eq,input.completed_values root,hTarget]
  simp only [hTargetEq,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
  apply WP.spec_bind (copy_indices_spec completed)
  intro current hCopy
  have hInit := flip_initial_invariant dimension completed predecessor discovery n rootIndex assignment root parent rank input rest current target hCopy hTarget
  apply WP.spec_bind (flip_sparse_path_loop_spec dimension completed predecessor discovery n rootIndex assignment root parent rank input rest current target
    0#usize false none hInit hTrace hNodup hPositive)
  rintro ⟨output,failure⟩ ⟨hFailure,hLength,hValues⟩
  dsimp only at hFailure hLength hValues ⊢
  subst failure
  exact (WP.spec_ok _).mpr ⟨rest,output,rfl,hTrace,hNodup,hPositive,hLength,hValues⟩

end SubtreeProofs.Rust.SparseSearch

end
