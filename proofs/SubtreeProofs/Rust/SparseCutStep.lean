module

public import SubtreeProofs.Rust.SparseCutBiInput
import Mathlib.Tactic

/-! # One actual sparse dual-search step with derived numeric safety -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseCut

open AssignmentNumericBounds

/-- The source step returns a genuine minimum allowed cut edge and physical
potential vectors satisfying the independent dual invariant. Coordinates refer
to the original matrix; the new tight edge crosses the actual search cut. -/
structure StepProgress (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128)
    (selectedRows selectedColumns : Slice Bool) (initialRows initialColumns : Vertex cost → ℤ)
    (increment : ℤ) (step : sparse.SparseStep) : Prop where
  minimum : MinimumCut cost rows columns selectedRows selectedColumns (some step.cut)
  rows_length : step.rows.length = cost.length
  columns_length : step.columns.length = cost.length
  rows_exact : potentialAt cost (alloc.vec.Vec.deref step.rows) = Assignment.adjustRows (potentialAt cost rows) (chosen cost selectedRows) step.cut.delta.val
  columns_exact : potentialAt cost (alloc.vec.Vec.deref step.columns) = Assignment.adjustColumns (potentialAt cost columns) (chosen cost selectedColumns) step.cut.delta.val
  feasible : Assignment.FeasibleOn (allowed cost) (matrix cost)
    (potentialAt cost (alloc.vec.Vec.deref step.rows)) (potentialAt cost (alloc.vec.Vec.deref step.columns))
  envelope : Assignment.BiEnvelope initialRows initialColumns
    (potentialAt cost (alloc.vec.Vec.deref step.rows)) (potentialAt cost (alloc.vec.Vec.deref step.columns)) (increment+step.cut.delta.val)
  account : Assignment.dualValue (potentialAt cost (alloc.vec.Vec.deref step.rows)) (potentialAt cost (alloc.vec.Vec.deref step.columns)) =
    Assignment.dualValue initialRows initialColumns+(increment+step.cut.delta.val)
  budget : increment+step.cut.delta.val ≤ cumulativeBound cost.length
  tight_edge : ∃ row column : Vertex cost,
    row.val = step.cut.row.val ∧ column.val = step.cut.column.val ∧
    row ∈ chosen cost selectedRows ∧ column ∉ chosen cost selectedColumns ∧ allowed cost row column ∧
    0 ≤ step.cut.delta.val ∧
    potentialAt cost (alloc.vec.Vec.deref step.rows) row+potentialAt cost (alloc.vec.Vec.deref step.columns) column = matrix cost row column

/-- The actual Rust selector/update composition succeeds from a feasible
one-excess-row paper state. Scanner ranges, update ranges and existence of an
allowed crossing edge are all consequences, not success/path certificates. -/
theorem advance_sparse_cut_spec (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128)
    (selectedRows selectedColumns : Slice Bool)
    (hrl : rows.length = cost.length) (hcl : columns.length = cost.length)
    (hsr : selectedRows.length = cost.length) (hsc : selectedColumns.length = cost.length)
    (hs : Square cost) (hn : cost.length ≤ U32.max)
    (initialRows initialColumns : Vertex cost → ℤ) (increment : ℤ)
    (hr : ∀ row, -costMagnitude ≤ initialRows row ∧ initialRows row ≤ 0)
    (hc : ∀ column, -costMagnitude ≤ initialColumns column ∧ initialColumns column ≤ 0)
    (henv : Assignment.BiEnvelope initialRows initialColumns (potentialAt cost rows) (potentialAt cost columns) increment)
    (ha : Assignment.dualValue (potentialAt cost rows) (potentialAt cost columns) = Assignment.dualValue initialRows initialColumns+increment)
    (hf : Assignment.FeasibleOn (allowed cost) (matrix cost) (potentialAt cost rows) (potentialAt cost columns))
    (hu : ∀ row column, allowed cost row column → matrix cost row column ≤ 0)
    (he : ∃ assignment : Equiv.Perm (Vertex cost), Assignment.Compatible (allowed cost) assignment)
    (hcard : (chosen cost selectedRows).card = (chosen cost selectedColumns).card+1) :
    sparse.advance_sparse_cut cost rows columns selectedRows selectedColumns ⦃ result => ∃ step,
      result = core.result.Result.Ok (some step) ∧ StepProgress cost rows columns selectedRows selectedColumns initialRows initialColumns increment step ⦄ := by
  unfold sparse.advance_sparse_cut
  apply WP.spec_bind (minimum_sparse_cut_bi_spec cost rows columns selectedRows selectedColumns hrl hcl hsr hsc hs hn
    initialRows initialColumns increment hr hc henv ha hf hu he hcard)
  rintro result ⟨cut,rfl,hMinimum,hAdjustment⟩
  obtain ⟨row,column,hRow,hColumn,hSelected,hUnselected,hAllowed,hDelta,hNonnegative,hFeasible,hTight⟩ := hAdjustment
  apply WP.spec_bind (adjust_sparse_cut_bi_safe_spec cost rows columns selectedRows selectedColumns cut.delta hrl hcl hsr hsc hn
    initialRows initialColumns increment hr hc henv ha hf hu he hcard hNonnegative
    (minimumCut_slack_bound cost rows columns selectedRows selectedColumns cut hMinimum))
  rintro result ⟨updatedRows,updatedColumns,rfl,hRowsLen,hColumnsLen,hRowsEq,hColumnsEq,hFeasible',hEnvelope,hAccount,hBudget⟩
  apply (WP.spec_ok _).mpr
  refine ⟨⟨cut,updatedRows,updatedColumns⟩,rfl,?_⟩
  refine ⟨hMinimum,hRowsLen,hColumnsLen,hRowsEq,hColumnsEq,hFeasible',hEnvelope,hAccount,hBudget,?_⟩
  refine ⟨row,column,hRow,hColumn,hSelected,hUnselected,hAllowed,hNonnegative,?_⟩
  change potentialAt cost (alloc.vec.Vec.deref updatedRows) row+potentialAt cost (alloc.vec.Vec.deref updatedColumns) column = _
  rw [hRowsEq,hColumnsEq]
  exact hTight

end SubtreeProofs.Rust.SparseCut

end
