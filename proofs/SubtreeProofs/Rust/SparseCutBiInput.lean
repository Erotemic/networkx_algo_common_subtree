module

public import SubtreeProofs.Rust.SparseCutUpdateSafety
import Mathlib.Tactic

/-! # Sparse scanner bounds derived from the two-sided paper invariant -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseCut

open AssignmentNumericBounds

theorem minimumCut_slack_bound (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128)
    (selectedRows selectedColumns : Slice Bool) (cut : sparse.SparseCut)
    (h : MinimumCut cost rows columns selectedRows selectedColumns (some cut)) :
    ∀ row ∈ chosen cost selectedRows, ∀ column, column ∉ chosen cost selectedColumns → allowed cost row column →
      cut.delta.val ≤ matrix cost row column-potentialAt cost rows row-potentialAt cost columns column := by
  intro row hRow column hColumn hEdge
  have hr := (mem_chosen cost selectedRows row).mp hRow
  have hc : selectedColumns.val[column.val]! = false := by
    cases hf : selectedColumns.val[column.val]! with
    | false => rfl
    | true => exact False.elim (hColumn ((mem_chosen cost selectedColumns column).mpr hf))
  obtain ⟨value,hValue⟩ := Option.ne_none_iff_exists'.mp hEdge
  rw [matrix_at_some cost row column value hValue]
  exact h.2 ((row.val,column.val),value.val-rows.val[row.val]!.val-columns.val[column.val]!.val)
    ⟨row.val,row.isLt,column.val,column.isLt,hr,hc,value,hValue,rfl⟩

theorem bi_envelope_values_bound {A : Type*} (initialRows initialColumns rows columns : A → ℤ)
    (increment : ℤ) (n : Nat) (hn : n ≤ U32.max)
    (henv : Assignment.BiEnvelope initialRows initialColumns rows columns increment)
    (hr : ∀ row, -costMagnitude ≤ initialRows row ∧ initialRows row ≤ 0)
    (hc : ∀ column, -costMagnitude ≤ initialColumns column ∧ initialColumns column ≤ 0)
    (hb : increment ≤ cumulativeBound n) :
    (∀ row, -potentialBound ≤ rows row ∧ rows row ≤ potentialBound) ∧
    (∀ column, -potentialBound ≤ columns column ∧ columns column ≤ potentialBound) := by
  have hsize : (n : ℤ) ≤ 4294967295 := by scalar_tac
  norm_num [cumulativeBound,costMagnitude] at hb
  constructor
  · intro row
    have hi := hr row
    have hl := henv.row_lower row
    have hu := henv.row_upper row
    norm_num [costMagnitude,potentialBound] at hi ⊢
    constructor <;> omega
  · intro column
    have hi := hc column
    have hl := henv.column_lower column
    have hu := henv.column_upper column
    norm_num [costMagnitude,potentialBound] at hi ⊢
    constructor <;> omega

/-- The scanner's representation and numeric input frame follows from the
actual two-sided feasible state and exact dual accounting. -/
theorem input_of_bi_state (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128)
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
    (he : ∃ assignment : Equiv.Perm (Vertex cost), Assignment.Compatible (allowed cost) assignment) :
    Input cost rows columns selectedRows selectedColumns := by
  have hb : increment ≤ cumulativeBound cost.length := by
    have hh := Assignment.total_increment_bound_both_on initialRows initialColumns (potentialAt cost rows) (potentialAt cost columns)
      costMagnitude 0 increment (fun row => (hr row).1) (fun column => (hc column).1) hu hf he ha
    simp only [Vertex,Fintype.card_fin,zero_add] at hh
    unfold cumulativeBound
    nlinarith
  have hv := bi_envelope_values_bound initialRows initialColumns _ _ increment cost.length hn henv hr hc hb
  exact ⟨hrl,hcl,hsr,hsc,hs,hn,fun index hi => hv.1 ⟨index,hi⟩,fun index hi => hv.2 ⟨index,hi⟩⟩

/-- Actual minimum sparse cut succeeds and returns an attained allowed edge
under the independent paper state; all scanner arithmetic bounds and cut
existence are derived rather than passed as certificates. -/
theorem minimum_sparse_cut_bi_spec (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128)
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
    sparse.minimum_sparse_cut cost rows columns selectedRows selectedColumns ⦃ result => ∃ cut,
      result = core.result.Result.Ok (some cut) ∧ MinimumCut cost rows columns selectedRows selectedColumns (some cut) ∧
      Adjustment cost rows columns selectedRows selectedColumns cut ⦄ := by
  have hi := input_of_bi_state cost rows columns selectedRows selectedColumns hrl hcl hsr hsc hs hn
    initialRows initialColumns increment hr hc henv ha hf hu he
  apply WP.spec_mono (minimum_sparse_cut_edges_spec cost rows columns selectedRows selectedColumns hi)
  rintro result ⟨output,hResult,hMinimum⟩
  cases output with
  | none => exact False.elim (hMinimum (originalEntry_exists cost rows columns selectedRows selectedColumns hcard he))
  | some cut => exact ⟨cut,hResult,hMinimum,minimumCut_adjustment cost rows columns selectedRows selectedColumns cut hMinimum hf⟩

end SubtreeProofs.Rust.SparseCut

end
