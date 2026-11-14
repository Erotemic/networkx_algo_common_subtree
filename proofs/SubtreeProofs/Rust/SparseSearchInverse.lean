module

public import SubtreeProofs.Rust.AssignmentInverseReconstruction
public import SubtreeProofs.Rust.AssignmentInitialization
import Mathlib.Tactic

/-! # Actual checked inverse table for the sparse search's completed assignment -/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseSearch

open AssignmentAdjustmentInvariant AssignmentColumnScan AssignmentScanInvariant

def InversePrefix (n : Usize) (assignment : Equiv.Perm (Fin n.val)) (inverse : alloc.vec.Vec Usize)
    (seen : alloc.vec.Vec Bool) (cursor : Nat) : Prop :=
  inverse.length = n.val ∧ seen.length = n.val ∧
  ∀ column : Fin n.val,
    seen.val[column.val]! = decide ((assignment.symm column).val < cursor) ∧
    inverse.val[column.val]!.val = if (assignment.symm column).val < cursor then (assignment.symm column).val else 0

theorem inverse_step_spec (completed : Slice Usize) (n row : Usize) (inverse : alloc.vec.Vec Usize) (seen : alloc.vec.Vec Bool)
    (hr : row.val < n.val) (hl : n.val = completed.length) (hi : inverse.length = n.val) (hs : seen.length = n.val)
    (hc : completed.val[row.val]!.val < n.val) (hf : seen.val[completed.val[row.val]!.val]! = false) :
    sparse_search.inverse_completed_loop.body completed n inverse seen none row ⦃ result => ∃ column next : Usize,
      column = completed.val[row.val]! ∧ next.val = row.val+1 ∧
      result = .cont (inverse.set column row,seen.set column true,none,next) ⦄ := by
  unfold sparse_search.inverse_completed_loop.body
  have hrow : row < n := hr
  have hread : row.val < completed.val.length := by change row.val < completed.length; omega
  simp only [hrow,↓reduceIte,core.option.Option.is_none]
  apply WP.spec_bind (Slice.index_usize_spec completed row (by omega))
  intro column hColumn
  have he : column = completed.val[row.val]! := by simpa only [getElem!_pos completed.val row.val hread] using hColumn
  have hb : ¬ column ≥ n := by rw [he]; scalar_tac
  simp only [hb,↓reduceIte,alloc.vec.Vec.index_slice_index,alloc.vec.Vec.index_mut_slice_index,Std.bind_assoc]
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec seen column (by rw [hs,he]; exact hc))
  intro flag hFlag
  have hfalse : flag = false := by
    have hseen : column.val < seen.val.length := by change column.val < seen.length; rw [hs,he]; exact hc
    have hh : flag = seen.val[column.val]! := by simpa only [getElem!_pos seen.val column.val hseen] using hFlag
    rw [hh,he,hf]
  simp only [hfalse,Bool.false_eq_true,↓reduceIte,Std.bind_assoc]
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec seen column (by rw [hs,he]; exact hc))
  rintro ⟨_,seenBack⟩ ⟨_,hSeen⟩
  simp only [uncurry_apply_pair,Std.bind_assoc]
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec inverse column (by rw [hi,he]; exact hc))
  rintro ⟨_,inverseBack⟩ ⟨_,hInverse⟩
  simp only [uncurry_apply_pair,bind_ok]
  apply WP.spec_bind (Usize.add_spec (x := row) (y := 1#usize) (by scalar_tac))
  intro next hNext
  exact (WP.spec_ok _).mpr ⟨column,next,he,by simpa only [UScalar.ofNatCore_val_eq] using hNext,by simp only [hSeen,hInverse]⟩

theorem inversePrefix_set (n : Usize) (assignment : Equiv.Perm (Fin n.val))
    (inverse : alloc.vec.Vec Usize) (seen : alloc.vec.Vec Bool) (row column : Usize)
    (hr : row.val < n.val) (hc : column.val = (assignment ⟨row.val,hr⟩).val)
    (h : InversePrefix n assignment inverse seen row.val) :
    InversePrefix n assignment (inverse.set column row) (seen.set column true) (row.val+1) := by
  refine ⟨by simpa using h.1,by simpa using h.2.1,?_⟩
  intro target
  have hcol : column.val < n.val := by rw [hc]; exact (assignment ⟨row.val,hr⟩).isLt
  by_cases he : target.val = column.val
  · have ht : target = assignment ⟨row.val,hr⟩ := Fin.ext (he.trans hc)
    have hv : (assignment.symm target).val = row.val := by rw [ht,Equiv.symm_apply_apply]
    rw [he,vec_set_self seen column true (by rw [h.2.1]; exact hcol),
      vec_set_self inverse column row (by rw [h.1]; exact hcol),hv]
    simp
  · have hn : (assignment.symm target).val ≠ row.val := by
      intro hh
      have ht : assignment.symm target = ⟨row.val,hr⟩ := Fin.ext hh
      have hh' := congrArg assignment ht
      rw [Equiv.apply_symm_apply] at hh'
      exact he ((congrArg Fin.val hh').trans hc.symm)
    rw [vec_set_other seen column true target.val (by rw [h.2.1]; exact target.isLt) (Ne.symm he),
      vec_set_other inverse column row target.val (by rw [h.1]; exact target.isLt) (Ne.symm he)]
    have hb : (assignment.symm target).val < row.val+1 ↔ (assignment.symm target).val < row.val := by omega
    simpa only [hb] using h.2.2 target

theorem inverse_completed_loop_spec (completed : Slice Usize) (n : Usize)
    (assignment : Equiv.Perm (Fin n.val)) (hl : n.val = completed.length)
    (hc : ∀ row : Fin n.val, completed.val[row.val]!.val = (assignment row).val)
    (inverse : alloc.vec.Vec Usize) (seen : alloc.vec.Vec Bool)
    (hi : InversePrefix n assignment inverse seen 0) :
    sparse_search.inverse_completed_loop completed n inverse seen none 0#usize ⦃ result =>
      result.2 = none ∧ result.1.length = n.val ∧
        ∀ column : Fin n.val, result.1.val[column.val]!.val = (assignment.symm column).val ⦄ := by
  unfold sparse_search.inverse_completed_loop
  apply loop.spec_decr_nat (fun state => n.val-state.2.2.2.val)
    (fun state => state.2.2.1 = none ∧ state.2.2.2.val ≤ n.val ∧
      InversePrefix n assignment state.1 state.2.1 state.2.2.2.val)
    _ _ _ ?_ ⟨rfl,by simp only [UScalar.ofNatCore_val_eq]; omega,hi⟩
  rintro ⟨current,flags,failure,row⟩ ⟨hFailure,hRow,hPrefix⟩
  dsimp only at hFailure hRow hPrefix ⊢
  subst failure
  by_cases hr : row.val < n.val
  · let vertex : Fin n.val := ⟨row.val,hr⟩
    have hColumn := hc vertex
    have hCol : completed.val[row.val]!.val < n.val := by rw [hColumn]; exact (assignment vertex).isLt
    have hFlag : flags.val[completed.val[row.val]!.val]! = false := by
      have hh := (hPrefix.2.2 (assignment vertex)).1
      rw [Equiv.symm_apply_apply] at hh
      simpa only [hColumn,vertex,lt_self_iff_false,decide_false] using hh
    apply WP.spec_mono (inverse_step_spec completed n row current flags hr hl hPrefix.1 hPrefix.2.1 hCol hFlag)
    rintro result ⟨column,next,hColumnEq,hNext,rfl⟩
    refine ⟨⟨rfl,by dsimp; omega,?_⟩,by dsimp; omega⟩
    simpa only [hNext] using inversePrefix_set n assignment current flags row column hr (by rw [hColumnEq]; exact hColumn) hPrefix
  · unfold sparse_search.inverse_completed_loop.body
    have hn : ¬ row < n := by scalar_tac
    simp only [hn,↓reduceIte,WP.spec_ok]
    have he : row.val = n.val := by omega
    refine ⟨True.intro,hPrefix.1,?_⟩
    intro column
    simpa only [he,ite_eq_left (assignment.symm column).isLt] using (hPrefix.2.2 column).2

/-- Actual validation/inversion succeeds for every represented permutation,
and returns its exact inverse in the same zero-based original coordinates. -/
theorem inverse_completed_spec (completed : Slice Usize) (n : Usize) (hl : n.val = completed.length)
    (assignment : Equiv.Perm (Fin n.val))
    (hc : ∀ row : Fin n.val, completed.val[row.val]!.val = (assignment row).val) :
    sparse_search.inverse_completed completed ⦃ result => ∃ inverse,
      result = core.result.Result.Ok inverse ∧ inverse.length = n.val ∧
        ∀ column : Fin n.val, inverse.val[column.val]!.val = (assignment.symm column).val ⦄ := by
  unfold sparse_search.inverse_completed
  have hs : Slice.len completed = n := UScalar.eq_of_val_eq ((Slice.len_val completed).trans hl.symm)
  rw [hs]
  apply WP.spec_bind (AssignmentInitialization.zeros_usize_spec n)
  intro inverse hInverse
  apply WP.spec_bind (AssignmentInitialization.unused_columns_spec n)
  intro seen hSeen
  have hInit : InversePrefix n assignment inverse seen 0 := by
    refine ⟨by simp only [alloc.vec.Vec.length,hInverse,List.length_replicate],by simp only [alloc.vec.Vec.length,hSeen,List.length_replicate],?_⟩
    intro column
    simp [hSeen,hInverse]
  apply WP.spec_bind (inverse_completed_loop_spec completed n assignment hl hc inverse seen hInit)
  rintro ⟨output,failure⟩ ⟨hFailure,hLen,hValues⟩
  dsimp only at hFailure hLen hValues ⊢
  subst failure
  exact (WP.spec_ok _).mpr ⟨output,rfl,hLen,hValues⟩

/-- Dimension-indexed form used by a caller whose graph vertices are already
indexed by the original cost matrix, independently of the slice length scalar. -/
theorem inverse_completed_dimension_spec (completed : Slice Usize) (dimension : Nat)
    (hl : completed.length = dimension) (assignment : Equiv.Perm (Fin dimension))
    (hc : ∀ row : Fin dimension, completed.val[row.val]!.val = (assignment row).val) :
    sparse_search.inverse_completed completed ⦃ result => ∃ inverse,
      result = core.result.Result.Ok inverse ∧ inverse.length = dimension ∧
        ∀ column : Fin dimension, inverse.val[column.val]!.val = (assignment.symm column).val ⦄ := by
  have he : dimension = (Slice.len completed).val := hl.symm.trans (Slice.len_val completed).symm
  subst dimension
  exact inverse_completed_spec completed (Slice.len completed) (Slice.len_val completed) assignment hc

end SubtreeProofs.Rust.SparseSearch

end
