module

public import SubtreeProofs.Rust.AssignmentAdjustmentLoop
public import SubtreeProofs.Shared.AssignmentPotentials
import Mathlib.Tactic

/-!
# Actual adjustment preserves the independent dual specification

The reserved machine slot zero is excluded from the mathematical assignment.
Every real row/column is represented by its one-based vector index.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentAdjustmentFeasibility

open AssignmentColumnScan AssignmentScanInvariant AssignmentAdjustment AssignmentAdjustmentInvariant AssignmentAdjustmentLoop

/-- The assignment's real indices omit the reserved machine slot zero. -/
def potential (n : Usize) (values : alloc.vec.Vec I128) (index : Fin n.val) : ℤ :=
  values.val[index.val+1]!.val

def selectedRows (n : Usize) (matched : Slice Usize) (used : Slice Bool) : Finset (Fin n.val) :=
  Finset.univ.filter (fun row => row.val+1 ∈ usedRows matched used (n.val+1))

def selectedColumns (n : Usize) (used : Slice Bool) : Finset (Fin n.val) :=
  Finset.univ.filter (fun col => col.val+1 ∈ usedIndices used (n.val+1))

@[simp] theorem mem_selectedRows (n : Usize) (matched : Slice Usize) (used : Slice Bool) (row : Fin n.val) :
    row ∈ selectedRows n matched used ↔ row.val+1 ∈ usedRows matched used (n.val+1) := by
  simp only [selectedRows, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem mem_selectedColumns (n : Usize) (used : Slice Bool) (col : Fin n.val) :
    col ∈ selectedColumns n used ↔ col.val+1 ∈ usedIndices used (n.val+1) := by
  simp only [selectedColumns, Finset.mem_filter, Finset.mem_univ, true_and]

theorem frames_rows (u v currentU currentV : alloc.vec.Vec I128) (matched : Slice Usize) (used : Slice Bool)
    (slack currentSlack : alloc.vec.Vec (Option I128)) (amount : I128) (n : Usize)
    (hu : n.val < u.length) (hframes : Frames u v matched used slack amount (n.val+1) currentU currentV currentSlack) :
    potential n currentU = Assignment.adjustRows (potential n u) (selectedRows n matched used) amount.val := by
  funext row
  have h := hframes.1.2 (row.val+1) (by have hr := row.isLt; omega)
  simpa only [potential, Assignment.adjustRows, mem_selectedRows, rowExpected] using h

theorem frames_columns (u v currentU currentV : alloc.vec.Vec I128) (matched : Slice Usize) (used : Slice Bool)
    (slack currentSlack : alloc.vec.Vec (Option I128)) (amount : I128) (n : Usize)
    (hv : n.val < v.length) (hframes : Frames u v matched used slack amount (n.val+1) currentU currentV currentSlack) :
    potential n currentV = Assignment.adjustColumns (potential n v) (selectedColumns n used) amount.val := by
  funext col
  have h := hframes.2.1.2 (col.val+1) (by have hc := col.isLt; omega)
  simpa only [potential, Assignment.adjustColumns, mem_selectedColumns, columnExpected] using h

/-- The numerical frame of the actual returned vectors implies the usual
mathematical cut update, so all independent dual inequalities are preserved. -/
theorem complete_feasible (u v : alloc.vec.Vec I128) (matched : Slice Usize) (used : Slice Bool)
    (slack : alloc.vec.Vec (Option I128)) (amount : I128) (n : Usize) (output : AdjustOutput)
    (matrix : Fin n.val → Fin n.val → ℤ) (hu : n.val < u.length) (hv : n.val < v.length)
    (hcomplete : CompleteAdjustment u v matched used slack amount n output)
    (hfeasible : Assignment.Feasible matrix (potential n u) (potential n v)) (hdelta : 0 ≤ amount.val)
    (hcut : ∀ row ∈ selectedRows n matched used, ∀ col, col ∉ selectedColumns n used →
      amount.val ≤ matrix row col - potential n u row - potential n v col) :
    Assignment.Feasible matrix (potential n output.2.1) (potential n output.2.2.1) := by
  rw [frames_rows u v _ _ matched used slack _ amount n hu hcomplete.2,
    frames_columns u v _ _ matched used slack _ amount n hv hcomplete.2]
  exact Assignment.adjust_feasible hfeasible hdelta hcut

/-- Existing tight edges whose endpoints move together remain exactly tight
in the vectors returned by the actual Rust loop. -/
theorem complete_preserves_tight_edge (u v : alloc.vec.Vec I128) (matched : Slice Usize) (used : Slice Bool)
    (slack : alloc.vec.Vec (Option I128)) (amount : I128) (n : Usize) (output : AdjustOutput)
    (matrix : Fin n.val → Fin n.val → ℤ) (hu : n.val < u.length) (hv : n.val < v.length)
    (hcomplete : CompleteAdjustment u v matched used slack amount n output) (row col : Fin n.val)
    (htight : potential n u row + potential n v col = matrix row col)
    (hlock : row ∈ selectedRows n matched used ↔ col ∈ selectedColumns n used) :
    potential n output.2.1 row + potential n output.2.2.1 col = matrix row col := by
  rw [frames_rows u v _ _ matched used slack _ amount n hu hcomplete.2,
    frames_columns u v _ _ matched used slack _ amount n hv hcomplete.2]
  exact Assignment.adjust_preserves_tight_edge matrix _ _ _ _ amount.val row col htight hlock

/-- An edge attaining the cut slack becomes tight in the actual returned
vectors, rather than merely in an idealized update. -/
theorem complete_creates_tight_edge (u v : alloc.vec.Vec I128) (matched : Slice Usize) (used : Slice Bool)
    (slack : alloc.vec.Vec (Option I128)) (amount : I128) (n : Usize) (output : AdjustOutput)
    (matrix : Fin n.val → Fin n.val → ℤ) (hu : n.val < u.length) (hv : n.val < v.length)
    (hcomplete : CompleteAdjustment u v matched used slack amount n output) (row col : Fin n.val)
    (hr : row ∈ selectedRows n matched used) (hc : col ∉ selectedColumns n used)
    (hslack : amount.val = matrix row col - potential n u row - potential n v col) :
    potential n output.2.1 row + potential n output.2.2.1 col = matrix row col := by
  rw [frames_rows u v _ _ matched used slack _ amount n hu hcomplete.2,
    frames_columns u v _ _ matched used slack _ amount n hv hcomplete.2]
  exact Assignment.adjust_creates_tight_edge matrix _ _ _ _ amount.val row col hr hc hslack

/-- Successful actual execution preserves the independent feasible dual
specification, assuming the cut and arithmetic premises supplied by the driver. -/
theorem adjust_potentials_feasible_spec (u v : alloc.vec.Vec I128) (matched : Slice Usize) (used : Slice Bool)
    (slack : alloc.vec.Vec (Option I128)) (amount : I128) (n : Usize)
    (bounds : Bounds u v matched used slack amount n) (hu : n.val < u.length)
    (matrix : Fin n.val → Fin n.val → ℤ)
    (hfeasible : Assignment.Feasible matrix (potential n u) (potential n v)) (hdelta : 0 ≤ amount.val)
    (hcut : ∀ row ∈ selectedRows n matched used, ∀ col, col ∉ selectedColumns n used →
      amount.val ≤ matrix row col - potential n u row - potential n v col) :
    adjust_potentials u v matched used slack amount n ⦃ output =>
      CompleteAdjustment u v matched used slack amount n output ∧
        Assignment.Feasible matrix (potential n output.2.1) (potential n output.2.2.1) ⦄ := by
  apply WP.spec_mono (adjust_potentials_spec u v matched used slack amount n bounds)
  intro output hcomplete
  exact ⟨hcomplete, complete_feasible u v matched used slack amount n output matrix hu bounds.v_len hcomplete hfeasible hdelta hcut⟩

end SubtreeProofs.Rust.AssignmentAdjustmentFeasibility

end
