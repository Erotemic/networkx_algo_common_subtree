module

public import SubtreeProofs.Rust.SparseCutUpdate
public import SubtreeProofs.Rust.SparseBiAdjustment
import Mathlib.Tactic

/-! # Derived safety and sparse feasibility of actual zero-based cut updates -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseCut

open AssignmentColumnScan AssignmentNumericBounds SparseBiAdjustment

theorem adjustedAt_rows (cost : Slice (alloc.vec.Vec (Option I64))) (values : Slice I128)
    (flags : Slice Bool) (delta : I128) (row : Vertex cost) :
    adjustedAt values flags delta true row.val =
      Assignment.adjustRows (potentialAt cost values) (chosen cost flags) delta.val row := by
  simp only [adjustedAt,adjustedValue,Assignment.adjustRows,mem_chosen,potentialAt,↓reduceIte]
  split <;> simp

theorem adjustedAt_columns (cost : Slice (alloc.vec.Vec (Option I64))) (values : Slice I128)
    (flags : Slice Bool) (delta : I128) (column : Vertex cost) :
    adjustedAt values flags delta false column.val =
      Assignment.adjustColumns (potentialAt cost values) (chosen cost flags) delta.val column := by
  simp only [adjustedAt,adjustedValue,Assignment.adjustColumns,mem_chosen,potentialAt,Bool.false_eq_true,↓reduceIte]
  split <;> simp

theorem updated_readback (values : Slice I128) (flags : Slice Bool) (delta : I128) (increasing : Bool)
    (updated : alloc.vec.Vec I128)
    (h : updated.val.map IScalar.val = (List.range values.length).map (adjustedAt values flags delta increasing)) :
    updated.length = values.length ∧ ∀ index, index < values.length →
      updated.val[index]!.val = adjustedAt values flags delta increasing index := by
  have hl := congrArg List.length h
  simp only [List.length_map,List.length_range] at hl
  refine ⟨hl,?_⟩
  intro index hi
  have hh := congrArg (fun xs : List ℤ => xs[index]!) h
  rw [getElem!_pos (updated.val.map IScalar.val) index (by simpa only [List.length_map] using hi.trans_le hl.symm.le),
    getElem!_pos ((List.range values.length).map (adjustedAt values flags delta increasing)) index (by simpa only [List.length_map,List.length_range] using hi)] at hh
  simpa only [List.getElem_map,List.getElem_range,getElem!_pos updated.val index (by omega)] using hh

/-- End-to-end safety for the actual zero-based update. The next feasible
ideal state bounds its total increment before any checked operation executes.
The returned vectors represent that state at every original coordinate. -/
theorem adjust_sparse_cut_bi_safe_spec (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128)
    (selectedRows selectedColumns : Slice Bool) (delta : I128)
    (hrl : rows.length = cost.length) (hcl : columns.length = cost.length)
    (hsr : selectedRows.length = cost.length) (hsc : selectedColumns.length = cost.length)
    (hn : cost.length ≤ U32.max)
    (initialRows initialColumns : Vertex cost → ℤ) (increment : ℤ)
    (hr : ∀ row, -costMagnitude ≤ initialRows row ∧ initialRows row ≤ 0)
    (hc : ∀ column, -costMagnitude ≤ initialColumns column ∧ initialColumns column ≤ 0)
    (henv : Assignment.BiEnvelope initialRows initialColumns (potentialAt cost rows) (potentialAt cost columns) increment)
    (ha : Assignment.dualValue (potentialAt cost rows) (potentialAt cost columns) = Assignment.dualValue initialRows initialColumns+increment)
    (hf : Assignment.FeasibleOn (allowed cost) (matrix cost) (potentialAt cost rows) (potentialAt cost columns))
    (hu : ∀ row column, allowed cost row column → matrix cost row column ≤ 0)
    (he : ∃ assignment : Equiv.Perm (Vertex cost), Assignment.Compatible (allowed cost) assignment)
    (hcard : (chosen cost selectedRows).card = (chosen cost selectedColumns).card+1)
    (hd : 0 ≤ delta.val)
    (hcut : ∀ row ∈ chosen cost selectedRows, ∀ column, column ∉ chosen cost selectedColumns → allowed cost row column →
      delta.val ≤ matrix cost row column-potentialAt cost rows row-potentialAt cost columns column) :
    sparse.adjust_sparse_cut rows columns selectedRows selectedColumns delta ⦃ result => ∃ updatedRows updatedColumns,
      result = core.result.Result.Ok (updatedRows,updatedColumns) ∧
      updatedRows.length = cost.length ∧ updatedColumns.length = cost.length ∧
      potentialAt cost (alloc.vec.Vec.deref updatedRows) = Assignment.adjustRows (potentialAt cost rows) (chosen cost selectedRows) delta.val ∧
      potentialAt cost (alloc.vec.Vec.deref updatedColumns) = Assignment.adjustColumns (potentialAt cost columns) (chosen cost selectedColumns) delta.val ∧
      Assignment.FeasibleOn (allowed cost) (matrix cost) (potentialAt cost (alloc.vec.Vec.deref updatedRows)) (potentialAt cost (alloc.vec.Vec.deref updatedColumns)) ∧
      Assignment.BiEnvelope initialRows initialColumns (potentialAt cost (alloc.vec.Vec.deref updatedRows))
        (potentialAt cost (alloc.vec.Vec.deref updatedColumns)) (increment+delta.val) ∧
      Assignment.dualValue (potentialAt cost (alloc.vec.Vec.deref updatedRows)) (potentialAt cost (alloc.vec.Vec.deref updatedColumns)) =
        Assignment.dualValue initialRows initialColumns+(increment+delta.val) ∧
      increment+delta.val ≤ cumulativeBound cost.length ⦄ := by
  have hbudget : increment+delta.val ≤ cumulativeBound cost.length := by
    have hh := Assignment.ideal_adjustment_increment_bound_both_on initialRows initialColumns (potentialAt cost rows) (potentialAt cost columns)
      (chosen cost selectedRows) (chosen cost selectedColumns) increment delta.val costMagnitude 0
      (fun row => (hr row).1) (fun column => (hc column).1) hu hf hd hcut hcard he ha
    simp only [Vertex,Fintype.card_fin,zero_add] at hh
    unfold cumulativeBound
    nlinarith
  have hnext := henv.adjust (chosen cost selectedRows) (chosen cost selectedColumns) delta.val hd
  have hfits := bi_envelope_values_fit initialRows initialColumns _ _ (increment+delta.val) cost.length hn hnext hr hc hbudget
  apply WP.spec_mono (adjust_sparse_cut_spec rows columns selectedRows selectedColumns delta (hcl.trans hrl.symm)
    (hsr.trans hrl.symm) (hsc.trans hrl.symm) (by omega) hd
    (by intro index hi; let row : Vertex cost := ⟨index,by omega⟩; rw [adjustedAt_rows cost rows selectedRows delta row]; exact hfits.1 row)
    (by intro index hi; let column : Vertex cost := ⟨index,by omega⟩; rw [adjustedAt_columns cost columns selectedColumns delta column]; exact hfits.2 column))
  rintro result ⟨updatedRows,updatedColumns,hResult,hRows,hColumns⟩
  obtain ⟨hRowLen,hRowValues⟩ := updated_readback rows selectedRows delta true updatedRows hRows
  obtain ⟨hColumnLen,hColumnValues⟩ := updated_readback columns selectedColumns delta false updatedColumns hColumns
  have hRowEq : potentialAt cost (alloc.vec.Vec.deref updatedRows) = Assignment.adjustRows (potentialAt cost rows) (chosen cost selectedRows) delta.val := by
    funext row
    simpa only [potentialAt,alloc.vec.Vec.deref,Slice.from_val] using
      (hRowValues row.val (by omega)).trans (adjustedAt_rows cost rows selectedRows delta row)
  have hColumnEq : potentialAt cost (alloc.vec.Vec.deref updatedColumns) = Assignment.adjustColumns (potentialAt cost columns) (chosen cost selectedColumns) delta.val := by
    funext column
    simpa only [potentialAt,alloc.vec.Vec.deref,Slice.from_val] using
      (hColumnValues column.val (by omega)).trans (adjustedAt_columns cost columns selectedColumns delta column)
  refine ⟨updatedRows,updatedColumns,hResult,hRowLen.trans hrl,hColumnLen.trans hcl,hRowEq,hColumnEq,?_,?_,?_,hbudget⟩
  · rw [hRowEq,hColumnEq]
    exact Assignment.adjust_feasible_on hf hd hcut
  · rw [hRowEq,hColumnEq]
    exact hnext
  · rw [hRowEq,hColumnEq,Assignment.adjust_dualValue_one _ _ _ _ _ hcard,ha]
    ring

end SubtreeProofs.Rust.SparseCut

end
