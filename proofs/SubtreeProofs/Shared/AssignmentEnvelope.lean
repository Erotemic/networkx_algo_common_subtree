module

public import SubtreeProofs.Shared.AssignmentPotentials
import Mathlib.Tactic

/-!
# Component envelopes and safe bounds before executing a cut update

A cumulative nonnegative adjustment bounds every row and column potential.
The ideal cut update is defined over the independent ordered ring, before
any checked machine operation. Feasibility and objective accounting bound
its new cumulative adjustment, avoiding circular overflow arguments.
-/

@[expose] public section

namespace SubtreeProofs.Assignment

variable {A K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

structure Envelope (initialRows rows columns : A → K) (increment : K) : Prop where
  nonnegative : 0 ≤ increment
  row_lower : ∀ row, initialRows row ≤ rows row
  row_upper : ∀ row, rows row ≤ initialRows row + increment
  column_lower : ∀ col, -increment ≤ columns col
  column_upper : ∀ col, columns col ≤ 0

omit [IsStrictOrderedRing K] in
theorem envelope_initial (initialRows : A → K) : Envelope initialRows initialRows (fun _ => 0) 0 := by
  constructor <;> simp

variable [DecidableEq A]

/-- Nonnegative cut increments preserve the component envelope for all
selected and unselected rows and columns. -/
theorem Envelope.adjust {initialRows rows columns : A → K} {increment : K}
    (h : Envelope initialRows rows columns increment) (selectedRows selectedColumns : Finset A)
    (delta : K) (hdelta : 0 ≤ delta) :
    Envelope initialRows (adjustRows rows selectedRows delta) (adjustColumns columns selectedColumns delta) (increment+delta) := by
  refine ⟨add_nonneg h.nonnegative hdelta,?_,?_,?_,?_⟩
  · intro row
    have hl := h.row_lower row
    by_cases hr : row ∈ selectedRows <;> simp only [adjustRows,hr,↓reduceIte] <;> linarith
  · intro row
    have hu := h.row_upper row
    by_cases hr : row ∈ selectedRows <;> simp only [adjustRows,hr,↓reduceIte] <;> linarith
  · intro col
    have hl := h.column_lower col
    by_cases hc : col ∈ selectedColumns <;> simp only [adjustColumns,hc,↓reduceIte] <;> linarith
  · intro col
    have hu := h.column_upper col
    by_cases hc : col ∈ selectedColumns <;> simp only [adjustColumns,hc,↓reduceIte] <;> linarith

omit [DecidableEq A] in
/-- A bounded matrix and lower-bounded initial rows bound all current reduced
costs using feasibility and the component envelope. -/
theorem Envelope.reduced_bounds {matrix : A → A → K} {initialRows rows columns : A → K} {increment bound : K}
    (h : Envelope initialRows rows columns increment) (hfeasible : Feasible matrix rows columns)
    (hcost : ∀ row col, -bound ≤ matrix row col ∧ matrix row col ≤ bound)
    (hinitial : ∀ row, -bound ≤ initialRows row ∧ initialRows row ≤ bound) (row col : A) :
    (-(2*bound+increment) ≤ matrix row col - rows row ∧ matrix row col - rows row ≤ 2*bound) ∧
      (0 ≤ matrix row col - rows row - columns col ∧ matrix row col - rows row - columns col ≤ 2*bound+increment) := by
  have hc := hcost row col
  have hi := hinitial row
  have hrl := h.row_lower row
  have hru := h.row_upper row
  have hcl := h.column_lower col
  have hcu := h.column_upper col
  have hf := hfeasible row col
  constructor <;> constructor <;> linarith

variable [Fintype A]

/-- Establish the next cumulative bound in the independent ideal state,
before requiring representability of any actual machine addition/subtraction. -/
theorem ideal_adjustment_increment_bound {matrix : A → A → K} (initialRows rows columns : A → K)
    (selectedRows selectedColumns : Finset A) (increment delta bound : K)
    (hlower : ∀ row, -bound ≤ initialRows row) (hupper : ∀ row col, matrix row col ≤ bound)
    (hfeasible : Feasible matrix rows columns) (hdelta : 0 ≤ delta)
    (hcut : ∀ row ∈ selectedRows, ∀ col, col ∉ selectedColumns → delta ≤ matrix row col - rows row - columns col)
    (hcard : selectedRows.card = selectedColumns.card+1)
    (haccount : dualValue rows columns = dualValue initialRows (fun _ => 0) + increment) :
    increment+delta ≤ 2*(Fintype.card A : K)*bound := by
  have hnext := adjust_feasible hfeasible hdelta hcut
  apply total_increment_bound initialRows (adjustRows rows selectedRows delta) (adjustColumns columns selectedColumns delta)
    bound (increment+delta) hlower hupper hnext
  rw [adjust_dualValue_one rows columns selectedRows selectedColumns delta hcard,haccount]
  ring

end SubtreeProofs.Assignment

end
