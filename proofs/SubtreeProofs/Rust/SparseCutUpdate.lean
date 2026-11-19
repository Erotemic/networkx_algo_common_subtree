module

public import SubtreeProofs.Rust.SparseCutAdjustment
public import SubtreeProofs.Rust.AssignmentArithmetic
public import SubtreeProofs.Rust.AssignmentCutFeasibility
import Mathlib.Tactic

/-! # Exact zero-based source updates of sparse potential slices -/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseCut

open AssignmentColumnScan

def adjustedValue (value : ℤ) (selected increasing : Bool) (delta : ℤ) : ℤ :=
  if selected then if increasing then value+delta else value-delta else value

def adjustedAt (values : Slice I128) (selected : Slice Bool) (delta : I128) (increasing : Bool) (index : Nat) : ℤ :=
  adjustedValue values.val[index]!.val selected.val[index]! increasing delta.val

theorem selected_update_spec (value delta : I128) (selected increasing : Bool)
    (hf : Fits128 (adjustedValue value.val selected increasing delta.val)) :
    (if increasing then sparse.increase_selected value selected delta else sparse.decrease_selected value selected delta) ⦃ result =>
      ∃ updated, result = core.result.Result.Ok updated ∧ updated.val = adjustedValue value.val selected increasing delta.val ⦄ := by
  cases increasing <;> cases selected <;>
    simp only [Bool.false_eq_true,↓reduceIte,adjustedValue,sparse.increase_selected,sparse.decrease_selected] at hf ⊢
  · exact (WP.spec_ok _).mpr ⟨value,rfl,rfl⟩
  · apply WP.spec_bind (AssignmentArithmetic.checked_sub_spec value delta hf.1 hf.2)
    rintro result ⟨updated,rfl,hu⟩
    exact (WP.spec_ok _).mpr ⟨updated,rfl,hu⟩
  · exact (WP.spec_ok _).mpr ⟨value,rfl,rfl⟩
  · apply WP.spec_bind (AssignmentArithmetic.checked_add_spec value delta hf.1 hf.2)
    rintro result ⟨updated,rfl,hu⟩
    exact (WP.spec_ok _).mpr ⟨updated,rfl,hu⟩

/-- The single-vector source loop returns every updated coordinate in order.
The range premises here are discharged by the independent envelope theorem
in the caller, before executing the checked updates. -/
theorem adjust_selected_spec (values : Slice I128) (selected : Slice Bool) (delta : I128) (increasing : Bool)
    (hl : selected.length = values.length) (hn : values.length ≤ U32.max)
    (hf : ∀ index, index < values.length → Fits128 (adjustedAt values selected delta increasing index)) :
    sparse.adjust_selected values selected delta increasing ⦃ result => ∃ updated,
      result = core.result.Result.Ok updated ∧ updated.val.map IScalar.val =
        (List.range values.length).map (adjustedAt values selected delta increasing) ⦄ := by
  unfold sparse.adjust_selected sparse.adjust_selected_loop
  apply loop.spec_decr_nat (fun state => values.length-state.2.val)
    (fun state => state.2.val ≤ values.length ∧ state.1.val.map IScalar.val =
      (List.range state.2.val).map (adjustedAt values selected delta increasing))
    _ _ _ ?_ (by simp only [UScalar.ofNatCore_val_eq,List.range_zero,List.map_nil,alloc.vec.Vec.new,alloc.vec.Vec.from_val]; exact ⟨Nat.zero_le _,True.intro⟩)
  rintro ⟨updated,index⟩ ⟨hb,hu⟩
  dsimp only at hb hu ⊢
  unfold sparse.adjust_selected_loop.body
  dsimp only
  split
  · rename_i hlt
    have hi : index.val < values.length := by have hv := Slice.len_val values; scalar_tac
    have hsi : index.val < selected.val.length := by change index.val < selected.length; omega
    have hread : (if increasing then do
        let value ← Slice.index_usize values index
        let flag ← Slice.index_usize selected index
        sparse.increase_selected value flag delta
      else do
        let value ← Slice.index_usize values index
        let flag ← Slice.index_usize selected index
        sparse.decrease_selected value flag delta) ⦃ result => ∃ value,
          result = core.result.Result.Ok value ∧ value.val = adjustedAt values selected delta increasing index.val ⦄ := by
      cases increasing <;> simp only [Bool.false_eq_true,↓reduceIte]
      all_goals
        apply WP.spec_bind (Slice.index_usize_spec values index hi)
        intro value hv
        apply WP.spec_bind (Slice.index_usize_spec selected index (by omega))
        intro flag hflag
        have hv' : value = values.val[index.val]! := by simpa only [getElem!_pos values.val index.val hi] using hv
        have hf' : flag = selected.val[index.val]! := by simpa only [getElem!_pos selected.val index.val hsi] using hflag
        rw [hv',hf']
      · simpa only [Bool.false_eq_true,↓reduceIte,adjustedAt] using selected_update_spec _ _ _ false (hf index.val hi)
      · simpa only [↓reduceIte,adjustedAt] using selected_update_spec _ _ _ true (hf index.val hi)
    apply WP.spec_bind hread
    rintro result ⟨value,rfl,hvalue⟩
    have hlen : updated.val.length = index.val := by
      have hh := congrArg List.length hu
      simpa only [List.length_map,List.length_range] using hh
    have hpush : updated.val.length < Usize.max := by
      rw [hlen]
      have hmax := AssignmentEntrypoint.u32_max_fits_usize
      scalar_tac
    apply WP.spec_bind (alloc.vec.Vec.push_spec updated value hpush)
    intro next hnext
    apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    intro nextIndex hIndex
    simp only [WP.spec_ok]
    refine ⟨⟨by scalar_tac,?_⟩,by scalar_tac⟩
    have hIndex' : nextIndex.val = index.val+1 := by scalar_tac
    rw [hnext,List.map_append,hu,hIndex',List.range_succ,List.map_append]
    simp only [List.map_cons,List.map_nil,hvalue]
  · rename_i hnot
    have he : index.val = values.length := by have hv := Slice.len_val values; scalar_tac
    exact (WP.spec_ok _).mpr ⟨updated,rfl,by simpa only [he] using hu⟩

/-- Actual public sparse update succeeds with exact original coordinate
readback when all independently computed updated coordinates fit i128. -/
theorem adjust_sparse_cut_spec (rows columns : Slice I128) (selectedRows selectedColumns : Slice Bool) (delta : I128)
    (hc : columns.length = rows.length) (hsr : selectedRows.length = rows.length)
    (hsc : selectedColumns.length = rows.length) (hn : rows.length ≤ U32.max) (hd : 0 ≤ delta.val)
    (hr : ∀ index, index < rows.length → Fits128 (adjustedAt rows selectedRows delta true index))
    (hv : ∀ index, index < columns.length → Fits128 (adjustedAt columns selectedColumns delta false index)) :
    sparse.adjust_sparse_cut rows columns selectedRows selectedColumns delta ⦃ result => ∃ updatedRows updatedColumns,
      result = core.result.Result.Ok (updatedRows,updatedColumns) ∧
      updatedRows.val.map IScalar.val = (List.range rows.length).map (adjustedAt rows selectedRows delta true) ∧
      updatedColumns.val.map IScalar.val = (List.range columns.length).map (adjustedAt columns selectedColumns delta false) ⦄ := by
  have hc' : Slice.len columns = Slice.len rows := UScalar.eq_of_val_eq (by simpa only [Slice.len_val] using hc)
  have hsr' : Slice.len selectedRows = Slice.len rows := UScalar.eq_of_val_eq (by simpa only [Slice.len_val] using hsr)
  have hsc' : Slice.len selectedColumns = Slice.len rows := UScalar.eq_of_val_eq (by simpa only [Slice.len_val] using hsc)
  unfold sparse.adjust_sparse_cut
  simp only [hc',hsr',hsc',bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
  apply WP.spec_bind (UScalar.cast_inBounds_spec .Usize core.num.U32.MAX AssignmentEntrypoint.u32_max_fits_usize)
  intro limit hLimit
  have hl : limit.val = U32.max := hLimit.trans AssignmentEntrypoint.u32_max_value
  have hsize : ¬ Slice.len rows > limit := by have hs := Slice.len_val rows; scalar_tac
  have hpositive : ¬ delta < 0#i128 := by scalar_tac
  simp only [hsize,hpositive,↓reduceIte]
  apply WP.spec_bind (adjust_selected_spec rows selectedRows delta true hsr hn hr)
  rintro first ⟨updatedRows,rfl,hRows⟩
  apply WP.spec_bind (adjust_selected_spec columns selectedColumns delta false (hsc.trans hc.symm) (by omega) hv)
  rintro second ⟨updatedColumns,rfl,hColumns⟩
  exact (WP.spec_ok _).mpr ⟨updatedRows,updatedColumns,rfl,hRows,hColumns⟩

end SubtreeProofs.Rust.SparseCut

end
