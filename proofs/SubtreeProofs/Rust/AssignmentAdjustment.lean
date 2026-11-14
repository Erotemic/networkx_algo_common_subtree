module

public import SubtreeProofs.Rust.AssignmentScanInvariant
public import SubtreeProofs.Rust.AssignmentArithmetic
import Mathlib.Tactic

/-!
# Actual checked potential-adjustment updates

These source-branch refinements record exact array writes. Their numeric
premises are explicit integer bounds, rather than an assumed loop result.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentAdjustment

open AssignmentColumnScan AssignmentScanInvariant

abbrev AdjustState := alloc.vec.Vec I128 × alloc.vec.Vec I128 × alloc.vec.Vec (Option I128) × Usize
abbrev AdjustOutput := core.result.Result Unit AssignmentError × alloc.vec.Vec I128 ×
  alloc.vec.Vec I128 × alloc.vec.Vec (Option I128)

/-- Used columns raise their assigned row and lower their own potential;
the slack table is unchanged. Both actual checked operations succeed. -/
theorem body_used_spec (matched : Slice Usize) (used : Slice Bool) (amount : I128)
    (n index : Usize) (u v : alloc.vec.Vec I128) (slack : alloc.vec.Vec (Option I128))
    (hc : index.val ≤ n.val) (hn : n.val < Usize.max)
    (hused : index.val < used.length) (hmatched : index.val < matched.length)
    (hv : index.val < v.length) (hu : matched.val[index.val]!.val < u.length)
    (hflag : used.val[index.val]! = true)
    (hadd : Fits128 (u.val[matched.val[index.val]!.val]!.val + amount.val))
    (hsub : Fits128 (v.val[index.val]!.val - amount.val)) :
    adjust_potentials_loop.body matched used amount n u v slack index ⦃ output =>
      ∃ rowValue colValue : I128, ∃ next : Usize,
        rowValue.val = u.val[matched.val[index.val]!.val]!.val + amount.val ∧
        colValue.val = v.val[index.val]!.val - amount.val ∧ next.val = index.val+1 ∧
        output = .cont (u.set matched.val[index.val]! rowValue, v.set index colValue, slack, next) ⦄ := by
  unfold adjust_potentials_loop.body
  rw [ite_eq_left (show index ≤ n from hc)]
  apply WP.spec_bind (Slice.index_usize_spec used index hused)
  intro flag hFlag
  have heFlag : flag = true := by
    rw [hFlag]
    simpa only [getElem!_pos used.val index.val hused] using hflag
  simp only [heFlag, ↓reduceIte]
  apply WP.spec_bind (Slice.index_usize_spec matched index hmatched)
  intro assigned hAssigned
  have hassigned : assigned = matched.val[index.val]! := by
    simpa only [getElem!_pos matched.val index.val hmatched] using hAssigned
  have huBound : assigned.val < u.length := by simpa only [hassigned] using hu
  simp only [alloc.vec.Vec.index_slice_index]
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec u assigned huBound)
  intro oldRow hOldRow
  have hrowValue : oldRow.val = u.val[matched.val[index.val]!.val]!.val := by
    rw [← hassigned, getElem!_pos u.val assigned.val huBound]
    exact congrArg IScalar.val hOldRow
  apply WP.spec_bind (AssignmentArithmetic.checked_add_spec oldRow amount
    (by rw [hrowValue]; exact hadd.1) (by rw [hrowValue]; exact hadd.2))
  rintro rowOption ⟨rowValue,hRowOption,hRowValue⟩
  subst rowOption
  simp only [alloc.vec.Vec.index_mut_slice_index]
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec u assigned huBound)
  rintro ⟨_,rowBack⟩ ⟨_,hRowBack⟩
  simp only [uncurry_apply_pair]
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec v index hv)
  intro oldCol hOldCol
  have hcolValue : oldCol.val = v.val[index.val]!.val := by
    simpa only [getElem!_pos v.val index.val hv] using congrArg IScalar.val hOldCol
  apply WP.spec_bind (AssignmentArithmetic.checked_sub_spec oldCol amount
    (by rw [hcolValue]; exact hsub.1) (by rw [hcolValue]; exact hsub.2))
  rintro colOption ⟨colValue,hColOption,hColValue⟩
  subst colOption
  simp only
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec v index hv)
  rintro ⟨_,colBack⟩ ⟨_,hColBack⟩
  simp only [uncurry_apply_pair]
  apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by have h := hn; scalar_tac))
  intro next hNext
  simp only [WP.spec_ok]
  exact ⟨rowValue,colValue,next, by simpa only [hrowValue] using hRowValue,
    by simpa only [hcolValue] using hColValue, by simpa using hNext,
    by simp only [hRowBack,hColBack,hassigned]⟩

/-- An absent slack at an unused column remains absent. -/
theorem body_unused_none_spec (matched : Slice Usize) (used : Slice Bool) (amount : I128)
    (n index : Usize) (u v : alloc.vec.Vec I128) (slack : alloc.vec.Vec (Option I128))
    (hc : index.val ≤ n.val) (hn : n.val < Usize.max)
    (hused : index.val < used.length) (hslack : index.val < slack.length)
    (hflag : used.val[index.val]! = false) (habsent : slack.val[index.val]! = none) :
    adjust_potentials_loop.body matched used amount n u v slack index ⦃ output =>
      ∃ next : Usize, next.val = index.val+1 ∧ output = .cont (u,v,slack,next) ⦄ := by
  unfold adjust_potentials_loop.body
  rw [ite_eq_left (show index ≤ n from hc)]
  apply WP.spec_bind (Slice.index_usize_spec used index hused)
  intro flag hFlag
  have heFlag : flag = false := by
    rw [hFlag]
    simpa only [getElem!_pos used.val index.val hused] using hflag
  simp only [heFlag, Bool.false_eq_true, ↓reduceIte, alloc.vec.Vec.index_slice_index]
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec slack index hslack)
  intro old hOld
  have heOld : old = none := by
    rw [hOld]
    simpa only [getElem!_pos slack.val index.val hslack] using habsent
  simp only [heOld]
  apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by have h := hn; scalar_tac))
  intro next hNext
  simp only [WP.spec_ok]
  exact ⟨next, by simpa using hNext, rfl⟩

/-- Every finite unused slack loses exactly the chosen adjustment. -/
theorem body_unused_some_spec (matched : Slice Usize) (used : Slice Bool) (amount : I128)
    (n index : Usize) (u v : alloc.vec.Vec I128) (slack : alloc.vec.Vec (Option I128)) (old : I128)
    (hc : index.val ≤ n.val) (hn : n.val < Usize.max)
    (hused : index.val < used.length) (hslack : index.val < slack.length)
    (hflag : used.val[index.val]! = false) (hpresent : slack.val[index.val]! = some old)
    (hsub : Fits128 (old.val - amount.val)) :
    adjust_potentials_loop.body matched used amount n u v slack index ⦃ output =>
      ∃ value : I128, ∃ next : Usize, value.val = old.val-amount.val ∧ next.val = index.val+1 ∧
        output = .cont (u,v,slack.set index (some value),next) ⦄ := by
  unfold adjust_potentials_loop.body
  rw [ite_eq_left (show index ≤ n from hc)]
  apply WP.spec_bind (Slice.index_usize_spec used index hused)
  intro flag hFlag
  have heFlag : flag = false := by
    rw [hFlag]
    simpa only [getElem!_pos used.val index.val hused] using hflag
  simp only [heFlag, Bool.false_eq_true, ↓reduceIte, alloc.vec.Vec.index_slice_index]
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec slack index hslack)
  intro current hCurrent
  have heCurrent : current = some old := by
    rw [hCurrent]
    simpa only [getElem!_pos slack.val index.val hslack] using hpresent
  simp only [heCurrent]
  apply WP.spec_bind (AssignmentArithmetic.checked_sub_spec old amount hsub.1 hsub.2)
  rintro valueOption ⟨value,hValueOption,hValue⟩
  subst valueOption
  simp only [alloc.vec.Vec.index_mut_slice_index]
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec slack index hslack)
  rintro ⟨_,back⟩ ⟨_,hback⟩
  simp only [uncurry_apply_pair]
  apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by have h := hn; scalar_tac))
  intro next hNext
  simp only [WP.spec_ok]
  exact ⟨value,next,hValue,by simpa using hNext,by simp only [hback]⟩

/-- Passing the dimension terminates with all current arrays. -/
theorem body_done_spec (matched : Slice Usize) (used : Slice Bool) (amount : I128)
    (n index : Usize) (u v : alloc.vec.Vec I128) (slack : alloc.vec.Vec (Option I128))
    (hc : n.val < index.val) :
    adjust_potentials_loop.body matched used amount n u v slack index ⦃ output =>
      output = .done (core.result.Result.Ok (),u,v,slack) ⦄ := by
  unfold adjust_potentials_loop.body
  have hnot : ¬ index ≤ n := by scalar_tac
  simp [hnot]

end SubtreeProofs.Rust.AssignmentAdjustment

end
