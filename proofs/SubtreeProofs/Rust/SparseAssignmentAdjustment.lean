module

public import SubtreeProofs.Rust.AssignmentSafeAdjustment
public import SubtreeProofs.Shared.AssignmentSparsePotentials
import Mathlib.Tactic

/-! # Actual shared potential updates preserve sparse duals with derived safe arithmetic -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseAssignmentAdjustment

open AssignmentColumnScan AssignmentAdjustmentInvariant AssignmentAdjustmentLoop AssignmentAdjustmentFeasibility
open AssignmentAdjustmentProgress AssignmentNumericBounds AssignmentSafeAdjustment

/-- Every checked update range follows from sparse dual feasibility, the
compatible perfect-assignment witness, component envelopes and source search
invariants. No finite value is substituted for a forbidden edge. -/
theorem derived_sparse_adjustment_bounds (u v : alloc.vec.Vec I128)
    (matched : Slice Usize) (used : Slice Bool) (slack : alloc.vec.Vec (Option I128)) (amount : I128) (n : Usize)
    (representation : Representation u v matched used slack n)
    (edges : Fin n.val → Fin n.val → Prop) (matrix : Fin n.val → Fin n.val → ℤ)
    (hupper : ∀ row column, edges row column → matrix row column ≤ costMagnitude)
    (hcompatible : ∃ assignment : Equiv.Perm (Fin n.val), Assignment.Compatible edges assignment)
    (initialRows : Fin n.val → ℤ) (increment : ℤ)
    (hinitial : ∀ row, -costMagnitude ≤ initialRows row ∧ initialRows row ≤ costMagnitude)
    (henvelope : Assignment.Envelope initialRows (potential n u) (potential n v) increment)
    (haccount : Assignment.dualValue (potential n u) (potential n v) = Assignment.dualValue initialRows (fun _ => 0) + increment)
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
    have h := Assignment.ideal_adjustment_increment_bound_on initialRows (potential n u) (potential n v)
      (selectedRows n matched used) (selectedColumns n used) increment amount.val costMagnitude
      (fun row => (hinitial row).1) hupper hfeasible hdelta hcut hcard hcompatible haccount
    simpa only [Fintype.card_fin,cumulativeBound] using h
  have hnextEnvelope := henvelope.adjust (selectedRows n matched used) (selectedColumns n used) amount.val hdelta
  have hfits := envelope_values_fit initialRows _ _ (increment+amount.val) n.val representation.n_size hnextEnvelope hinitial hnextBound
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
theorem adjust_potentials_sparse_safe_spec (u v : alloc.vec.Vec I128)
    (matched : Slice Usize) (used : Slice Bool) (slack : alloc.vec.Vec (Option I128)) (amount : I128) (n : Usize)
    (representation : Representation u v matched used slack n)
    (edges : Fin n.val → Fin n.val → Prop) (matrix : Fin n.val → Fin n.val → ℤ)
    (hupper : ∀ row column, edges row column → matrix row column ≤ costMagnitude)
    (hcompatible : ∃ assignment : Equiv.Perm (Fin n.val), Assignment.Compatible edges assignment)
    (initialRows : Fin n.val → ℤ) (increment : ℤ)
    (hinitial : ∀ row, -costMagnitude ≤ initialRows row ∧ initialRows row ≤ costMagnitude)
    (henvelope : Assignment.Envelope initialRows (potential n u) (potential n v) increment)
    (haccount : Assignment.dualValue (potential n u) (potential n v) = Assignment.dualValue initialRows (fun _ => 0) + increment)
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
      Assignment.Envelope initialRows (potential n output.2.1) (potential n output.2.2.1) (increment+amount.val) ∧
      Assignment.dualValue (potential n output.2.1) (potential n output.2.2.1) =
        Assignment.dualValue initialRows (fun _ => 0)+(increment+amount.val) ∧
      output.2.2.1.val[0]!.val = -(increment+amount.val) ∧
      increment+amount.val ≤ cumulativeBound n.val ⦄ := by
  obtain ⟨hBounds,hBudget⟩ := derived_sparse_adjustment_bounds u v matched used slack amount n representation edges matrix
    hupper hcompatible initialRows increment hinitial henvelope haccount hreserved hfeasible hdelta hcut hinjective hzero hrows hslackUpper hminimum
  apply WP.spec_mono (adjust_potentials_spec u v matched used slack amount n hBounds)
  intro output hComplete
  have hNumeric := complete_numeric_invariants u v matched used slack amount n output representation.u_len representation.v_len hComplete
    initialRows increment henvelope haccount hreserved hdelta hinjective hzero hrows
  refine ⟨hComplete,?_,hNumeric.1,hNumeric.2.1,hNumeric.2.2,hBudget⟩
  rw [frames_rows u v _ _ matched used slack _ amount n representation.u_len hComplete.2,
    frames_columns u v _ _ matched used slack _ amount n representation.v_len hComplete.2]
  exact Assignment.adjust_feasible_on hfeasible hdelta hcut

end SubtreeProofs.Rust.SparseAssignmentAdjustment

end
