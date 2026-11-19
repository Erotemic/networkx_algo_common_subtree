module

public import SubtreeProofs.Rust.AssignmentNumericBounds
public import SubtreeProofs.Rust.AssignmentAdjustmentProgress
import Mathlib.Tactic

/-!
# Deriving every checked-adjustment range from search invariants

The independent ideal update first establishes its new feasible dual and
cumulative bound. Component envelopes then prove the actual row additions,
column subtractions (including reserved zero), and finite slack subtractions
fit i128. No premise assumes success of those machine operations.
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace SubtreeProofs.Rust.AssignmentSafeAdjustment

open AssignmentColumnScan AssignmentAdjustmentInvariant AssignmentAdjustmentLoop AssignmentAdjustmentFeasibility
open AssignmentAdjustmentProgress AssignmentNumericBounds

structure Representation (u v : alloc.vec.Vec I128) (matched : Slice Usize) (used : Slice Bool)
    (slack : alloc.vec.Vec (Option I128)) (n : Usize) : Prop where
  n_max : n.val < Usize.max
  n_size : n.val ≤ U32.max
  matched_len : n.val < matched.length
  used_len : n.val < used.length
  u_len : n.val < u.length
  v_len : n.val < v.length
  slack_len : n.val < slack.length

/-- All numeric premises of the actual complete adjustment loop follow from
independent dual accounting, feasibility, cut minima and component envelopes. -/
theorem derived_adjustment_bounds (cost : Slice (alloc.vec.Vec I64)) (u v : alloc.vec.Vec I128)
    (matched : Slice Usize) (used : Slice Bool) (slack : alloc.vec.Vec (Option I128)) (amount : I128) (n : Usize)
    (representation : Representation u v matched used slack n) (initialRows : Fin n.val → ℤ) (increment : ℤ)
    (hinitial : ∀ row, -costMagnitude ≤ initialRows row ∧ initialRows row ≤ costMagnitude)
    (henvelope : Assignment.Envelope initialRows (potential n u) (potential n v) increment)
    (haccount : Assignment.dualValue (potential n u) (potential n v) = Assignment.dualValue initialRows (fun _ => 0) + increment)
    (hreserved : v.val[0]!.val = -increment)
    (hfeasible : Assignment.Feasible (AssignmentReconstruction.matrix cost n) (potential n u) (potential n v))
    (hdelta : 0 ≤ amount.val)
    (hcut : ∀ row ∈ selectedRows n matched used, ∀ col, col ∉ selectedColumns n used →
      amount.val ≤ AssignmentReconstruction.matrix cost n row col - potential n u row - potential n v col)
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
    have h := Assignment.ideal_adjustment_increment_bound initialRows (potential n u) (potential n v)
      (selectedRows n matched used) (selectedColumns n used) increment amount.val costMagnitude
      (fun row => (hinitial row).1) (fun row col => (cost_bounds cost n row col).2) hfeasible hdelta hcut hcard haccount
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


/-- Exact frames from successful actual execution preserve component envelopes
and the independent dual/reserved-slot accounting identities. -/
theorem complete_numeric_invariants (u v : alloc.vec.Vec I128) (matched : Slice Usize) (used : Slice Bool)
    (slack : alloc.vec.Vec (Option I128)) (amount : I128) (n : Usize) (output : AssignmentAdjustment.AdjustOutput)
    (hu : n.val < u.length) (hv : n.val < v.length)
    (hcomplete : CompleteAdjustment u v matched used slack amount n output)
    (initialRows : Fin n.val → ℤ) (increment : ℤ)
    (henvelope : Assignment.Envelope initialRows (potential n u) (potential n v) increment)
    (haccount : Assignment.dualValue (potential n u) (potential n v) = Assignment.dualValue initialRows (fun _ => 0) + increment)
    (hreserved : v.val[0]!.val = -increment) (hdelta : 0 ≤ amount.val)
    (hinjective : UsedInjective matched used n) (hzero : used.val[0]! = true)
    (hrows : ∀ col, col ≤ n.val → used.val[col]! = true → 0 < matched.val[col]!.val ∧ matched.val[col]!.val ≤ n.val) :
    Assignment.Envelope initialRows (potential n output.2.1) (potential n output.2.2.1) (increment+amount.val) ∧
      Assignment.dualValue (potential n output.2.1) (potential n output.2.2.1) =
        Assignment.dualValue initialRows (fun _ => 0) + (increment+amount.val) ∧
      output.2.2.1.val[0]!.val = -(increment+amount.val) := by
  refine ⟨?_,?_,?_⟩
  · rw [frames_rows u v _ _ matched used slack _ amount n hu hcomplete.2,
      frames_columns u v _ _ matched used slack _ amount n hv hcomplete.2]
    exact henvelope.adjust _ _ amount.val hdelta
  · rw [complete_dual_progress u v matched used slack amount n output hu hv hcomplete hinjective hzero
      (fun col hb hf => (hrows col hb hf).1) (fun col hb hf => (hrows col hb hf).2),haccount]
    ring
  · rw [complete_reserved_column u v matched used slack amount n output hv hcomplete hzero,hreserved]
    ring

end SubtreeProofs.Rust.AssignmentSafeAdjustment

end
