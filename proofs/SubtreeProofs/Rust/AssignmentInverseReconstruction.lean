module

public import SubtreeProofs.Rust.AssignmentAugmentationMatching
public import SubtreeProofs.Shared.AssignmentPointerDecoding
import Mathlib.Tactic

/-!
# Actual inversion of a complete row-pointer assignment

The first reconstruction loop writes each positive column into its assigned
row's zero-based slot. The prefix specification is stated using the independent
inverse permutation, whose existence follows from complete partial matching.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentInverseReconstruction

open AssignmentColumnScan AssignmentScanInvariant AssignmentAugmentationMatching AssignmentAdjustmentInvariant

abbrev InverseState := Option AssignmentError × alloc.vec.Vec Usize × Usize
abbrev InverseOutput := Option AssignmentError × alloc.vec.Vec Usize

/-- Exact inverse slots for processed columns, with unprocessed rows zero. -/
def InversePrefix (n : Usize) (assignment : Equiv.Perm (Fin n.val)) (result : alloc.vec.Vec Usize) (cursor : Nat) : Prop :=
  result.length = n.val ∧ ∀ row : Fin n.val, result.val[row.val]!.val =
    if (assignment row).val+1 < cursor then (assignment row).val else 0

/-- One source iteration checks the input pointer, writes the two zero-based
indices and advances the column without a failure. -/
theorem body_step_spec (matched : Slice Usize) (n column : Usize) (result : alloc.vec.Vec Usize)
    (hc : column.val ≤ n.val) (hpositive : 0 < column.val) (hn : n.val < Usize.max)
    (hmatched : n.val < matched.length) (hlen : result.length = n.val)
    (hp : 0 < matched.val[column.val]!.val) (hb : matched.val[column.val]!.val ≤ n.val) :
    reconstruct_assignment_loop0.body matched n none result column ⦃ output =>
      ∃ index value next : Usize, index.val = matched.val[column.val]!.val-1 ∧ value.val = column.val-1 ∧
        next.val = column.val+1 ∧ output = .cont (none,result.set index value,next) ⦄ := by
  unfold reconstruct_assignment_loop0.body
  have hcol : column ≤ n := hc
  simp only [hcol, ↓reduceIte, core.option.Option.is_none]
  apply WP.spec_bind (Slice.index_usize_spec matched column (lt_of_le_of_lt hc hmatched))
  intro assigned hAssigned
  have ha : assigned = matched.val[column.val]! := by
    simpa only [getElem!_pos matched.val column.val (lt_of_le_of_lt hc hmatched)] using hAssigned
  have ha0 : assigned ≠ 0#usize := by rw [ha]; scalar_tac
  have hal : ¬ assigned > n := by rw [ha]; scalar_tac
  simp only [ha0,hal,↓reduceIte,Std.bind_assoc]
  apply WP.spec_bind (Usize.sub_spec (x := column) (y := 1#usize) (by scalar_tac))
  intro value hvalue
  apply WP.spec_bind (Usize.sub_spec (x := assigned) (y := 1#usize) (by rw [ha]; scalar_tac))
  intro index hindex
  have hib : index.val < result.length := by rw [hlen]; rw [ha] at hindex; scalar_tac
  simp only [alloc.vec.Vec.index_mut_slice_index]
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec result index hib)
  rintro ⟨_,back⟩ ⟨_,hback⟩
  simp only [uncurry_apply_pair,bind_ok]
  apply WP.spec_bind (Usize.add_spec (x := column) (y := 1#usize) (by scalar_tac))
  intro next hnext
  simp only [WP.spec_ok]
  exact ⟨index,value,next,by simpa only [ha,UScalar.ofNatCore_val_eq] using hindex.1,by simpa using hvalue.1,
    by simpa using hnext,by simp only [hback]⟩

theorem inversePrefix_set (n : Usize) (assignment : Equiv.Perm (Fin n.val))
    (result : alloc.vec.Vec Usize) (column index value : Usize)
    (hprefix : InversePrefix n assignment result column.val) (hindex : index.val < n.val)
    (hposition : (assignment ⟨index.val,hindex⟩).val+1 = column.val)
    (hvalue : value.val = column.val-1) (_hpositive : 0 < column.val) :
    InversePrefix n assignment (result.set index value) (column.val+1) := by
  refine ⟨by simpa using hprefix.1,?_⟩
  intro row
  by_cases he : row.val = index.val
  · have hr : row = ⟨index.val,hindex⟩ := Fin.ext he
    rw [he,vec_set_self result index value (by rw [hprefix.1]; exact hindex)]
    have hp : (assignment row).val+1 = column.val := by rw [hr]; exact hposition
    rw [ite_eq_left (by omega)]
    omega
  · have hother : (assignment row).val+1 ≠ column.val := by
      intro hp
      have hv : (assignment row).val = (assignment ⟨index.val,hindex⟩).val := by omega
      have heq := assignment.injective (Fin.ext hv)
      exact he (congrArg Fin.val heq)
    rw [vec_set_other result index value row.val (by rw [hprefix.1]; exact row.isLt) (Ne.symm he)]
    have hguard : (assignment row).val+1 < column.val+1 ↔ (assignment row).val+1 < column.val := by omega
    simpa only [hguard] using hprefix.2 row

/-- The entire actual inverse-table loop returns the exact zero-based inverse
permutation and leaves its failure flag absent. -/
theorem reconstruct_inverse_loop_spec (matched : Slice Usize) (n : Usize) (result : alloc.vec.Vec Usize)
    (assignment : Equiv.Perm (Fin n.val)) (hinverse : ∀ row, matched.val[(assignment row).val+1]!.val = row.val+1)
    (hmatched : n.val < matched.length) (hn : n.val < Usize.max)
    (hinit : result.val = List.replicate n.val 0#usize) :
    reconstruct_assignment_loop0 matched n none result 1#usize ⦃ output =>
      output.1 = none ∧ InversePrefix n assignment output.2 (n.val+1) ⦄ := by
  unfold reconstruct_assignment_loop0
  apply loop.spec_decr_nat (fun state => n.val+1-state.2.2.val)
    (fun (state : InverseState) => state.1 = none ∧ 0 < state.2.2.val ∧ state.2.2.val ≤ n.val+1 ∧
      InversePrefix n assignment state.2.1 state.2.2.val)
    (fun (output : InverseOutput) => output.1 = none ∧ InversePrefix n assignment output.2 (n.val+1)) _ _ ?_ ?_
  · rintro ⟨failure,current,column⟩ ⟨hfailure,hpositive,hcursor,hprefix⟩
    dsimp only at hfailure hpositive hcursor hprefix ⊢
    subst failure
    by_cases hc : column.val ≤ n.val
    · let col : Fin n.val := ⟨column.val-1,by omega⟩
      let row := assignment.symm col
      have hcol : (assignment row).val+1 = column.val := by
        simp only [row,Equiv.apply_symm_apply,col]
        omega
      have hptr : matched.val[column.val]!.val = row.val+1 := by
        simpa only [hcol] using hinverse row
      apply WP.spec_mono (body_step_spec matched n column current hc hpositive hn hmatched hprefix.1
        (by rw [hptr]; omega) (by rw [hptr]; have hr := row.isLt; omega))
      rintro output ⟨index,value,next,hindex,hvalue,hnext,houtput⟩
      subst output
      have hi : index.val = row.val := by rw [hptr] at hindex; omega
      have hib : index.val < n.val := by rw [hi]; exact row.isLt
      have hposition : (assignment ⟨index.val,hib⟩).val+1 = column.val := by
        have he : (⟨index.val,hib⟩ : Fin n.val) = row := Fin.ext hi
        rw [he]
        exact hcol
      refine ⟨⟨rfl,by dsimp; omega,by dsimp; omega,?_⟩,by dsimp; omega⟩
      simpa only [hnext] using inversePrefix_set n assignment current column index value hprefix hib hposition hvalue hpositive
    · unfold reconstruct_assignment_loop0.body
      have hnot : ¬ column ≤ n := by scalar_tac
      simp only [hnot,↓reduceIte,WP.spec_ok]
      have he : column.val = n.val+1 := by omega
      exact ⟨True.intro,by simpa only [he] using hprefix⟩
  · refine ⟨rfl,by simp,by simp,?_⟩
    refine ⟨by simp [hinit],?_⟩
    intro row
    simp [hinit]

end SubtreeProofs.Rust.AssignmentInverseReconstruction

end
