module

public import SubtreeProofs.Rust.SparseSearchInitialization
import Mathlib.Tactic

/-! # Actual sparse augmenting-path entry point with no supplied path certificate -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseSearch

open SparseCut AssignmentNumericBounds

/-- Actual Rust sparse search succeeds for every represented completed
permutation with a feasible tight single-deficit seed and the paper's numeric
initialization invariant. No path, inverse table, rank, loop result or machine
arithmetic-success certificate is supplied. Returned predecessor edges retain
original coordinates, are allowed and tight, and follow decreasing ranks. -/
theorem find_sparse_augmenting_path_spec (cost : Slice (alloc.vec.Vec (Option I64)))
    (rows columns : alloc.vec.Vec I128) (completed : Slice Usize) (rootIndex : Usize)
    (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost)
    (hr : rootIndex.val = root.val)
    (hrl : rows.length = cost.length) (hcl : columns.length = cost.length) (hpl : completed.length = cost.length)
    (hPermutation : ∀ row : Vertex cost, completed.val[row.val]!.val = (assignment row).val)
    (hs : Square cost) (hn : cost.length ≤ U32.max)
    (initialRows initialColumns : Vertex cost → ℤ) (increment : ℤ)
    (hInitialRows : ∀ row, -costMagnitude ≤ initialRows row ∧ initialRows row ≤ 0)
    (hInitialColumns : ∀ column, -costMagnitude ≤ initialColumns column ∧ initialColumns column ≤ 0)
    (hEnvelope : Assignment.BiEnvelope initialRows initialColumns (potentialAt cost (alloc.vec.Vec.deref rows)) (potentialAt cost (alloc.vec.Vec.deref columns)) increment)
    (hAccount : Assignment.dualValue (potentialAt cost (alloc.vec.Vec.deref rows)) (potentialAt cost (alloc.vec.Vec.deref columns)) =
      Assignment.dualValue initialRows initialColumns+increment)
    (hFeasible : Assignment.FeasibleOn (allowed cost) (matrix cost) (potentialAt cost (alloc.vec.Vec.deref rows)) (potentialAt cost (alloc.vec.Vec.deref columns)))
    (hTight : ∀ row, row ≠ root → potentialAt cost (alloc.vec.Vec.deref rows) row+
      potentialAt cost (alloc.vec.Vec.deref columns) (assignment row) = matrix cost row (assignment row))
    (hUpper : ∀ row column, allowed cost row column → matrix cost row column ≤ 0)
    (hCompatible : ∃ replacement : Equiv.Perm (Vertex cost), Assignment.Compatible (allowed cost) replacement) :
    sparse_search.find_sparse_augmenting_path cost rows columns completed rootIndex ⦃ result => ∃ search,
      result = core.result.Result.Ok search ∧ PathCertificate cost assignment root initialRows initialColumns search ⦄ := by
  have hrLen : alloc.vec.Vec.len rows = Slice.len cost := UScalar.eq_of_val_eq (by simpa only [alloc.vec.Vec.len_val,Slice.len_val] using hrl)
  have hcLen : alloc.vec.Vec.len columns = Slice.len cost := UScalar.eq_of_val_eq (by simpa only [alloc.vec.Vec.len_val,Slice.len_val] using hcl)
  have hpLen : Slice.len completed = Slice.len cost := UScalar.eq_of_val_eq (by simpa only [Slice.len_val] using hpl)
  have hRoot : rootIndex.val < cost.length := by rw [hr]; exact root.isLt
  unfold sparse_search.find_sparse_augmenting_path
  simp only [hrLen,hcLen,hpLen,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
  apply WP.spec_bind (UScalar.cast_inBounds_spec .Usize core.num.U32.MAX AssignmentEntrypoint.u32_max_fits_usize)
  intro limit hLimit
  have hLimitVal : limit.val = U32.max := hLimit.trans AssignmentEntrypoint.u32_max_value
  have hSize : ¬ Slice.len cost > limit := by have hl := Slice.len_val cost; scalar_tac
  have hRootBound : ¬ rootIndex ≥ Slice.len cost := by have hl := Slice.len_val cost; scalar_tac
  simp only [hSize,hRootBound,↓reduceIte]
  apply WP.spec_bind (inverse_completed_dimension_spec completed cost.length hpl assignment hPermutation)
  rintro result ⟨inverse,rfl,hInverseLen,hInverseValues⟩
  apply WP.spec_bind (Slice.index_usize_spec completed rootIndex (by omega))
  intro target hTarget
  have hTargetEq : target.val = (assignment root).val := by
    have he : target = completed.val[rootIndex.val]! := by
      simpa only [getElem!_pos completed.val rootIndex.val (by change rootIndex.val < completed.length; omega)] using hTarget
    rw [he,hr,hPermutation root]
  apply WP.spec_bind (AssignmentInitialization.unused_columns_spec (Slice.len cost))
  intro flags hFlags
  apply WP.spec_bind (AssignmentInitialization.zeros_usize_spec (Slice.len cost))
  intro parents hParents
  have hFlagValues : flags.val = List.replicate cost.length false := by simpa only [Slice.len_val] using hFlags
  have hParentValues : parents.val = List.replicate cost.length 0#usize := by simpa only [Slice.len_val] using hParents
  have hFlagsLen : flags.length = cost.length := by simp only [alloc.vec.Vec.length,hFlagValues,List.length_replicate]
  simp only [alloc.vec.Vec.index_mut_slice_index]
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec flags rootIndex (by omega))
  rintro ⟨_,back⟩ ⟨_,hBack⟩
  simp only [uncurry_apply_pair,hBack]
  have hInput : Input cost (Slice.len cost) assignment root inverse target initialRows initialColumns :=
    ⟨Slice.len_val cost,hn,hs,hInverseLen,hInverseValues,hTargetEq,hInitialRows,hInitialColumns,hUpper,hCompatible⟩
  have hInit := initial_invariant cost assignment root rootIndex hr initialRows initialColumns increment rows columns hrl hcl
    flags parents hFlagValues hParentValues hFeasible hTight hEnvelope hAccount
  apply WP.spec_bind (find_sparse_augmenting_path_loop_spec cost (Slice.len cost) assignment root inverse target initialRows initialColumns increment
    rows columns (flags.set rootIndex true) flags parents parents 0#usize true none hInput hInit)
  rintro ⟨newRows,newColumns,predecessor,discovery,steps,failure⟩ hStopped
  obtain ⟨hFailure,hCertificate⟩ := Stopped.certificate cost (Slice.len cost) assignment root inverse target initialRows initialColumns hInput _ hStopped
  dsimp only at hFailure hCertificate ⊢
  subst failure
  exact (WP.spec_ok _).mpr ⟨⟨newRows,newColumns,predecessor,discovery,target,steps⟩,rfl,hCertificate⟩

end SubtreeProofs.Rust.SparseSearch

end
