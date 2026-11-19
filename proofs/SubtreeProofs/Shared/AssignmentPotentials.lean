module

public import SubtreeProofs.Shared.AssignmentDuality
import Mathlib.Tactic

/-!
# Cut adjustments and bounds for exact Hungarian potentials

These are independent matrix/potential statements used to verify the actual
integer implementation's adjustment phase and machine-arithmetic bounds.
-/

@[expose] public section

namespace SubtreeProofs.Assignment

variable {A K : Type*} [DecidableEq A] [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

def adjustRows (rows : A → K) (selected : Finset A) (delta : K) (row : A) : K :=
  rows row + if row ∈ selected then delta else 0

def adjustColumns (columns : A → K) (selected : Finset A) (delta : K) (col : A) : K :=
  columns col - if col ∈ selected then delta else 0

/-- The cut's minimum slack may be added to its row potentials and subtracted
from its column potentials while preserving every dual inequality. -/
theorem adjust_feasible {matrix : A → A → K} {rows columns : A → K}
    {selectedRows selectedColumns : Finset A} {delta : K}
    (hfeasible : Feasible matrix rows columns) (hdelta : 0 ≤ delta)
    (hcut : ∀ row ∈ selectedRows, ∀ col, col ∉ selectedColumns →
      delta ≤ matrix row col - rows row - columns col) :
    Feasible matrix (adjustRows rows selectedRows delta) (adjustColumns columns selectedColumns delta) := by
  intro row col
  have h := hfeasible row col
  by_cases hr : row ∈ selectedRows <;> by_cases hc : col ∈ selectedColumns
  · simp only [adjustRows, adjustColumns, hr, hc, ↓reduceIte]
    linarith
  · have hslack := hcut row hr col hc
    simp only [adjustRows, adjustColumns, hr, hc, ↓reduceIte, sub_zero]
    linarith
  · simp only [adjustRows, adjustColumns, hr, hc, ↓reduceIte, add_zero]
    linarith
  · simpa [adjustRows, adjustColumns, hr, hc] using h

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- A matching edge whose endpoints lie in the cut together retains its
exact tightness under the potential adjustment. -/
theorem adjust_preserves_tight_edge (matrix : A → A → K) (rows columns : A → K)
    (selectedRows selectedColumns : Finset A) (delta : K) (row col : A)
    (htight : rows row + columns col = matrix row col)
    (hlock : row ∈ selectedRows ↔ col ∈ selectedColumns) :
    adjustRows rows selectedRows delta row + adjustColumns columns selectedColumns delta col = matrix row col := by
  by_cases hr : row ∈ selectedRows
  · have hc := hlock.mp hr
    simp only [adjustRows, adjustColumns, hr, hc, ↓reduceIte]
    linear_combination htight
  · have hc : col ∉ selectedColumns := fun hc => hr (hlock.mpr hc)
    simpa [adjustRows, adjustColumns, hr, hc] using htight

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- An edge attaining the cut slack becomes exactly tight. -/
theorem adjust_creates_tight_edge (matrix : A → A → K) (rows columns : A → K)
    (selectedRows selectedColumns : Finset A) (delta : K) (row col : A)
    (hr : row ∈ selectedRows) (hc : col ∉ selectedColumns)
    (hslack : delta = matrix row col - rows row - columns col) :
    adjustRows rows selectedRows delta row + adjustColumns columns selectedColumns delta col = matrix row col := by
  simp only [adjustRows, adjustColumns, hr, hc, ↓reduceIte, sub_zero]
  linear_combination hslack

variable [Fintype A]

/-- A finite nonempty cut with a remaining column has an attained slack
adjustment. Feasibility makes it nonnegative, and an attaining edge becomes tight. -/
theorem exists_cut_adjustment {matrix : A → A → K} {rows columns : A → K}
    (selectedRows selectedColumns : Finset A) (hrows : selectedRows.Nonempty)
    (hcolumns : ∃ col, col ∉ selectedColumns) (hfeasible : Feasible matrix rows columns) :
    ∃ delta row col, row ∈ selectedRows ∧ col ∉ selectedColumns ∧
      delta = matrix row col - rows row - columns col ∧ 0 ≤ delta ∧
      (∀ r ∈ selectedRows, ∀ c, c ∉ selectedColumns → delta ≤ matrix r c - rows r - columns c) ∧
      Feasible matrix (adjustRows rows selectedRows delta) (adjustColumns columns selectedColumns delta) ∧
      adjustRows rows selectedRows delta row + adjustColumns columns selectedColumns delta col = matrix row col := by
  classical
  let candidates := selectedRows.product (Finset.univ \ selectedColumns)
  have hn : candidates.Nonempty := by
    obtain ⟨col,hcol⟩ := hcolumns
    exact hrows.product ⟨col, by simp [hcol]⟩
  obtain ⟨pair, hpair, hmin⟩ := Finset.exists_min_image candidates
    (fun p => matrix p.1 p.2 - rows p.1 - columns p.2) hn
  have hp : pair.1 ∈ selectedRows ∧ pair.2 ∉ selectedColumns := by
    simpa only [candidates, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and] using hpair
  let delta := matrix pair.1 pair.2 - rows pair.1 - columns pair.2
  have hd : 0 ≤ delta := by
    have hf := hfeasible pair.1 pair.2
    dsimp only [delta]
    linarith
  have hcut : ∀ r ∈ selectedRows, ∀ c, c ∉ selectedColumns →
      delta ≤ matrix r c - rows r - columns c := by
    intro r hr c hc
    exact hmin (r,c) (by simp [candidates, hr, hc])
  exact ⟨delta, pair.1, pair.2, hp.1, hp.2, rfl, hd, hcut,
    adjust_feasible hfeasible hd hcut,
    adjust_creates_tight_edge matrix rows columns selectedRows selectedColumns delta pair.1 pair.2 hp.1 hp.2 rfl⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem adjust_dualValue (rows columns : A → K) (selectedRows selectedColumns : Finset A) (delta : K) :
    dualValue (adjustRows rows selectedRows delta) (adjustColumns columns selectedColumns delta) =
      dualValue rows columns + (selectedRows.card : K) * delta - (selectedColumns.card : K) * delta := by
  simp only [dualValue, adjustRows, adjustColumns, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_ite_mem_eq, Finset.sum_ite_mem_eq]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The alternating-tree cut has one more row than real columns, so each
adjustment raises its feasible dual objective by exactly delta. -/
theorem adjust_dualValue_one (rows columns : A → K) (selectedRows selectedColumns : Finset A) (delta : K)
    (hcard : selectedRows.card = selectedColumns.card + 1) :
    dualValue (adjustRows rows selectedRows delta) (adjustColumns columns selectedColumns delta) =
      dualValue rows columns + delta := by
  rw [adjust_dualValue, hcard]
  push_cast
  ring

omit [DecidableEq A] in
/-- A uniform matrix upper bound also bounds every feasible dual objective. -/
theorem dualValue_le_card_mul {matrix : A → A → K} {rows columns : A → K} (bound : K)
    (hfeasible : Feasible matrix rows columns) (hcost : ∀ row col, matrix row col ≤ bound) :
    dualValue rows columns ≤ (Fintype.card A : K) * bound := by
  apply (weak_duality hfeasible (Equiv.refl A)).trans
  unfold cost
  calc
    _ ≤ ∑ _ : A, bound := Finset.sum_le_sum (fun row _ => hcost row row)
    _ = _ := by simp

omit [DecidableEq A] in
/-- The total nonnegative potential increments will therefore fit a bound
linear in the input dimension and the original cost magnitude. -/
theorem total_increment_bound {matrix : A → A → K} (initialRows finalRows finalColumns : A → K)
    (bound increment : K) (hlower : ∀ row, -bound ≤ initialRows row)
    (hupper : ∀ row col, matrix row col ≤ bound)
    (hfeasible : Feasible matrix finalRows finalColumns)
    (hvalue : dualValue finalRows finalColumns = dualValue initialRows (fun _ => 0) + increment) :
    increment ≤ 2 * (Fintype.card A : K) * bound := by
  have hfinal := dualValue_le_card_mul bound hfeasible hupper
  have hstart : -(Fintype.card A : K) * bound ≤ dualValue initialRows (fun _ => 0) := by
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset A)) (fun row _ => hlower row)
    simpa [dualValue] using hsum
  linarith

end SubtreeProofs.Assignment

end
