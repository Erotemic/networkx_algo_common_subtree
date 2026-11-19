module

public import SubtreeProofs.Rust.AssignmentSafeAdjustment
public import SubtreeProofs.Shared.AssignmentBiEnvelope
import Mathlib.Tactic

/-! # Actual sparse updates with nonzero initial potentials on both sides -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseBiAdjustment

open AssignmentColumnScan AssignmentAdjustmentInvariant AssignmentAdjustmentLoop AssignmentAdjustmentFeasibility
open AssignmentAdjustmentProgress AssignmentNumericBounds AssignmentSafeAdjustment

/-- The paper's nonpositive initial potentials on both sides obey the same
conservative i128 range as the zero-column dense initialization. -/
theorem bi_envelope_values_fit {A : Type*} (initialRows initialColumns rows columns : A → ℤ)
    (increment : ℤ) (n : Nat) (hn : n ≤ U32.max)
    (henvelope : Assignment.BiEnvelope initialRows initialColumns rows columns increment)
    (hinitial : ∀ row, -costMagnitude ≤ initialRows row ∧ initialRows row ≤ 0)
    (hcolumns : ∀ column, -costMagnitude ≤ initialColumns column ∧ initialColumns column ≤ 0)
    (hbudget : increment ≤ cumulativeBound n) :
    (∀ row, Fits128 (rows row)) ∧ (∀ column, Fits128 (columns column)) := by
  have hm : 0 ≤ costMagnitude := by norm_num [costMagnitude]
  constructor
  · intro row
    apply fits128_of_bound n _ hn
    · unfold reducedBound
      linarith [henvelope.row_lower row,(hinitial row).1,henvelope.nonnegative]
    · unfold reducedBound
      linarith [henvelope.row_upper row,(hinitial row).2]
  · intro column
    apply fits128_of_bound n _ hn
    · unfold reducedBound
      linarith [henvelope.column_lower column,(hcolumns column).1]
    · exact (henvelope.column_upper column).trans ((hcolumns column).2.trans (reducedBound_nonnegative n))

/-- Every checked update range follows from sparse dual feasibility, the
compatible perfect-assignment witness, component envelopes and source search
invariants. No finite value is substituted for a forbidden edge. -/
theorem derived_bi_adjustment_bounds (u v : alloc.vec.Vec I128)
    (matched : Slice Usize) (used : Slice Bool) (slack : alloc.vec.Vec (Option I128)) (amount : I128) (n : Usize)
    (representation : Representation u v matched used slack n)
    (edges : Fin n.val → Fin n.val → Prop) (matrix : Fin n.val → Fin n.val → ℤ)
    (hupper : ∀ row column, edges row column → matrix row column ≤ 0)
    (hcompatible : ∃ assignment : Equiv.Perm (Fin n.val), Assignment.Compatible edges assignment)
    (initialRows initialColumns : Fin n.val → ℤ) (increment : ℤ)
    (hinitial : ∀ row, -costMagnitude ≤ initialRows row ∧ initialRows row ≤ 0)
    (hcolumns : ∀ column, -costMagnitude ≤ initialColumns column ∧ initialColumns column ≤ 0)
    (henvelope : Assignment.BiEnvelope initialRows initialColumns (potential n u) (potential n v) increment)
    (haccount : Assignment.dualValue (potential n u) (potential n v) = Assignment.dualValue initialRows initialColumns + increment)
    (hreserved : v.val[0]!.val = -increment)
    (hfeasible : Assignment.FeasibleOn edges matrix (potential n u) (potential n v))
    (hdelta : 0 ≤ amount.val)
    (hcut : ∀ row ∈ selectedRows n matched used, ∀ col, col ∉ selectedColumns n used → edges row col →
      amount.val ≤ matrix row col - potential n u row - potential n v col)
    (hinjective : UsedInjective matched used n) (hzero : used.val[0]! = true)
    (hrows : ∀ col, col ≤ n.val → used.val[col]! = true → 0 < matched.val[col]!.val ∧ matched.val[col]!.val ≤ n.val)
    (hslackUpper : ∀ col, col ≤ n.val → used.val[col]! = false → ∀ value : I128,
      slack.val[col]! = some value → value.val ≤ reducedBound n.val)
    (hminimum : ∀ col, col ≤ n.val → used.val[col]! = false → ∀ value : I128,
      slack.val[col]! = some value → amount.val ≤ value.val) :
    Bounds u v matched used slack amount n ∧ increment+amount.val ≤ cumulativeBound n.val := by
  have hcard := selected_cardinality n matched used hinjective hzero
    (fun col hb hf => (hrows col hb hf).1) (fun col hb hf => (hrows col hb hf).2)
  have hnextBound : increment+amount.val ≤ cumulativeBound n.val := by
    have h := Assignment.ideal_adjustment_increment_bound_both_on initialRows initialColumns (potential n u) (potential n v)
      (selectedRows n matched used) (selectedColumns n used) increment amount.val costMagnitude 0
      (fun row => (hinitial row).1) (fun column => (hcolumns column).1) hupper hfeasible hdelta hcut hcard hcompatible haccount
    simp only [Fintype.card_fin,zero_add] at h
    unfold cumulativeBound
    nlinarith
  have hnextEnvelope := henvelope.adjust (selectedRows n matched used) (selectedColumns n used) amount.val hdelta
  have hfits := bi_envelope_values_fit initialRows initialColumns _ _ (increment+amount.val) n.val representation.n_size hnextEnvelope hinitial hcolumns hnextBound
  refine ⟨?_,hnextBound⟩
  refine ⟨representation.n_max,representation.matched_len,representation.used_len,representation.v_len,
    representation.slack_len,?_,hinjective,?_,?_,?_⟩
  · intro col hb hf
    exact lt_of_le_of_lt (hrows col hb hf).2 representation.u_len
  · intro col hb hf
    have hr := hrows col hb hf
    let row : Fin n.val := ⟨matched.val[col]!.val-1,by omega⟩
    have hri : row.val+1 = matched.val[col]!.val := by dsimp only [row]; omega
    have hmem : row ∈ selectedRows n matched used := by
      apply (mem_selectedRows n matched used row).mpr
      exact (mem_usedRows matched used _ _).mpr ⟨col,by omega,hf,hri.symm⟩
    simpa only [Assignment.adjustRows,hmem,↓reduceIte,potential,hri] using hfits.1 row
  · intro col hb hf
    by_cases hz : col = 0
    · rw [hz,hreserved]
      have he : -increment-amount.val = -(increment+amount.val) := by ring
      rw [he]
      exact reserved_value_fits n.val (increment+amount.val) representation.n_size hnextEnvelope.nonnegative hnextBound
    · let index : Fin n.val := ⟨col-1,by omega⟩
      have hci : index.val+1 = col := by dsimp only [index]; omega
      have hmem : index ∈ selectedColumns n used := by
        apply (mem_selectedColumns n used index).mpr
        rw [hci]
        exact (mem_usedIndices used _ _).mpr ⟨by omega,hf⟩
      simpa only [Assignment.adjustColumns,hmem,↓reduceIte,potential,hci] using hfits.2 index
  · intro col hb hf value hv
    exact slack_subtraction_fits n.val value.val amount.val representation.n_size
      (hslackUpper col hb hf value hv) hdelta (hminimum col hb hf value hv)


/-- Actual checked Rust potential updates preserve sparse dual feasibility,
the component envelope and objective accounting. Every machine range premise
is derived above from the independent search state and sparse cut conditions. -/
theorem adjust_potentials_bi_safe_spec (u v : alloc.vec.Vec I128)
    (matched : Slice Usize) (used : Slice Bool) (slack : alloc.vec.Vec (Option I128)) (amount : I128) (n : Usize)
    (representation : Representation u v matched used slack n)
    (edges : Fin n.val → Fin n.val → Prop) (matrix : Fin n.val → Fin n.val → ℤ)
    (hupper : ∀ row column, edges row column → matrix row column ≤ 0)
    (hcompatible : ∃ assignment : Equiv.Perm (Fin n.val), Assignment.Compatible edges assignment)
    (initialRows initialColumns : Fin n.val → ℤ) (increment : ℤ)
    (hinitial : ∀ row, -costMagnitude ≤ initialRows row ∧ initialRows row ≤ 0)
    (hcolumns : ∀ column, -costMagnitude ≤ initialColumns column ∧ initialColumns column ≤ 0)
    (henvelope : Assignment.BiEnvelope initialRows initialColumns (potential n u) (potential n v) increment)
    (haccount : Assignment.dualValue (potential n u) (potential n v) = Assignment.dualValue initialRows initialColumns + increment)
    (hreserved : v.val[0]!.val = -increment)
    (hfeasible : Assignment.FeasibleOn edges matrix (potential n u) (potential n v))
    (hdelta : 0 ≤ amount.val)
    (hcut : ∀ row ∈ selectedRows n matched used, ∀ col, col ∉ selectedColumns n used → edges row col →
      amount.val ≤ matrix row col - potential n u row - potential n v col)
    (hinjective : UsedInjective matched used n) (hzero : used.val[0]! = true)
    (hrows : ∀ col, col ≤ n.val → used.val[col]! = true → 0 < matched.val[col]!.val ∧ matched.val[col]!.val ≤ n.val)
    (hslackUpper : ∀ col, col ≤ n.val → used.val[col]! = false → ∀ value : I128,
      slack.val[col]! = some value → value.val ≤ reducedBound n.val)
    (hminimum : ∀ col, col ≤ n.val → used.val[col]! = false → ∀ value : I128,
      slack.val[col]! = some value → amount.val ≤ value.val) :
    adjust_potentials u v matched used slack amount n ⦃ output =>
      CompleteAdjustment u v matched used slack amount n output ∧
      Assignment.FeasibleOn edges matrix (potential n output.2.1) (potential n output.2.2.1) ∧
      Assignment.BiEnvelope initialRows initialColumns (potential n output.2.1) (potential n output.2.2.1) (increment+amount.val) ∧
      Assignment.dualValue (potential n output.2.1) (potential n output.2.2.1) =
        Assignment.dualValue initialRows initialColumns+(increment+amount.val) ∧
      output.2.2.1.val[0]!.val = -(increment+amount.val) ∧
      increment+amount.val ≤ cumulativeBound n.val ⦄ := by
  obtain ⟨hBounds,hBudget⟩ := derived_bi_adjustment_bounds u v matched used slack amount n representation edges matrix
    hupper hcompatible initialRows initialColumns increment hinitial hcolumns henvelope haccount hreserved hfeasible hdelta hcut hinjective hzero hrows hslackUpper hminimum
  apply WP.spec_mono (adjust_potentials_spec u v matched used slack amount n hBounds)
  intro output hComplete
  refine ⟨hComplete,?_,?_,?_,?_,hBudget⟩
  · rw [frames_rows u v _ _ matched used slack _ amount n representation.u_len hComplete.2,
      frames_columns u v _ _ matched used slack _ amount n representation.v_len hComplete.2]
    exact Assignment.adjust_feasible_on hfeasible hdelta hcut
  · rw [frames_rows u v _ _ matched used slack _ amount n representation.u_len hComplete.2,
      frames_columns u v _ _ matched used slack _ amount n representation.v_len hComplete.2]
    exact henvelope.adjust _ _ amount.val hdelta
  · rw [complete_dual_progress u v matched used slack amount n output representation.u_len representation.v_len hComplete hinjective hzero
      (fun col hb hf => (hrows col hb hf).1) (fun col hb hf => (hrows col hb hf).2),haccount]
    ring
  · rw [complete_reserved_column u v matched used slack amount n output representation.v_len hComplete hzero,hreserved]
    ring

end SubtreeProofs.Rust.SparseBiAdjustment

end
