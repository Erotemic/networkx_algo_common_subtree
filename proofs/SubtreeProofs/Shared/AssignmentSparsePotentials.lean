module

public import SubtreeProofs.Shared.AssignmentPotentials
public import SubtreeProofs.Shared.AssignmentDualityOn
import Mathlib.Tactic

/-! # Sparse alternating cuts: an allowed crossing edge and safe dual progress -/

@[expose] public section

namespace SubtreeProofs.Assignment

variable {A K : Type*} [DecidableEq A]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A compatible perfect assignment must cross every cut containing more rows
than columns. This supplies a real allowed edge even in a sparse graph. -/
theorem exists_allowed_crossing (edges : A → A → Prop) (assignment : Equiv.Perm A)
    (h : Compatible edges assignment) (selectedRows selectedColumns : Finset A)
    (hcard : selectedColumns.card < selectedRows.card) :
    ∃ row ∈ selectedRows, ∃ column, column ∉ selectedColumns ∧ edges row column := by
  have hi : (selectedRows.image assignment).card = selectedRows.card :=
    Finset.card_image_iff.mpr (fun _ _ _ _ he => assignment.injective he)
  have hc : selectedColumns.card < (selectedRows.image assignment).card := by omega
  obtain ⟨column,hColumn,hOutside⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  obtain ⟨row,hRow,he⟩ := Finset.mem_image.mp hColumn
  exact ⟨row,hRow,column,hOutside,he ▸ h row⟩

/-- The source cut adjustment preserves feasibility on actual edges only;
forbidden pairs impose no fictitious finite reduced cost. -/
theorem adjust_feasible_on {edges : A → A → Prop} {matrix : A → A → K} {rows columns : A → K}
    {selectedRows selectedColumns : Finset A} {delta : K}
    (hf : FeasibleOn edges matrix rows columns) (hd : 0 ≤ delta)
    (hcut : ∀ row ∈ selectedRows, ∀ column, column ∉ selectedColumns → edges row column →
      delta ≤ matrix row column-rows row-columns column) :
    FeasibleOn edges matrix (adjustRows rows selectedRows delta) (adjustColumns columns selectedColumns delta) := by
  intro row column he
  have hb := hf row column he
  by_cases hr : row ∈ selectedRows <;> by_cases hc : column ∈ selectedColumns
  · simp only [adjustRows,adjustColumns,hr,hc,↓reduceIte]
    linarith
  · have hh := hcut row hr column hc he
    simp only [adjustRows,adjustColumns,hr,hc,↓reduceIte,sub_zero]
    linarith
  · simp only [adjustRows,adjustColumns,hr,hc,↓reduceIte,add_zero]
    linarith
  · simpa only [adjustRows,adjustColumns,hr,hc,↓reduceIte,add_zero,sub_zero] using hb

variable [Fintype A]

/-- Every one-excess-row sparse alternating cut admits a nonnegative attained
slack adjustment, preserves sparse feasibility and creates an actual tight edge.
The needed edge is derived from a compatible perfect assignment. -/
theorem exists_cut_adjustment_on (edges : A → A → Prop) (matrix : A → A → K) (rows columns : A → K)
    (selectedRows selectedColumns : Finset A) (hcard : selectedRows.card = selectedColumns.card+1)
    (hf : FeasibleOn edges matrix rows columns)
    (he : ∃ assignment : Equiv.Perm A, Compatible edges assignment) :
    ∃ delta row column, row ∈ selectedRows ∧ column ∉ selectedColumns ∧ edges row column ∧
      delta = matrix row column-rows row-columns column ∧ 0 ≤ delta ∧
      (∀ r ∈ selectedRows, ∀ c, c ∉ selectedColumns → edges r c → delta ≤ matrix r c-rows r-columns c) ∧
      FeasibleOn edges matrix (adjustRows rows selectedRows delta) (adjustColumns columns selectedColumns delta) ∧
      adjustRows rows selectedRows delta row+adjustColumns columns selectedColumns delta column = matrix row column := by
  classical
  obtain ⟨assignment,hAssignment⟩ := he
  obtain ⟨start,hStart,finish,hFinish,hEdge⟩ := exists_allowed_crossing edges assignment hAssignment selectedRows selectedColumns (by omega)
  let candidates := (selectedRows.product (Finset.univ \ selectedColumns)).filter (fun pair => edges pair.1 pair.2)
  have hn : candidates.Nonempty := ⟨(start,finish),by simp only [candidates,Finset.mem_filter,Finset.product_eq_sprod,
    Finset.mem_product,Finset.mem_sdiff,Finset.mem_univ,true_and]; exact ⟨⟨hStart,hFinish⟩,hEdge⟩⟩
  obtain ⟨pair,hPair,hMinimum⟩ := Finset.exists_min_image candidates (fun p => matrix p.1 p.2-rows p.1-columns p.2) hn
  have hp : (pair.1 ∈ selectedRows ∧ pair.2 ∉ selectedColumns) ∧ edges pair.1 pair.2 := by
    simpa only [candidates,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_sdiff,Finset.mem_univ,true_and] using hPair
  let delta := matrix pair.1 pair.2-rows pair.1-columns pair.2
  have hd : 0 ≤ delta := by have hh := hf pair.1 pair.2 hp.2; dsimp only [delta]; linarith
  have hcut : ∀ r ∈ selectedRows, ∀ c, c ∉ selectedColumns → edges r c → delta ≤ matrix r c-rows r-columns c := by
    intro r hr c hc hedge
    exact hMinimum (r,c) (by simp [candidates,hr,hc,hedge])
  exact ⟨delta,pair.1,pair.2,hp.1.1,hp.1.2,hp.2,rfl,hd,hcut,adjust_feasible_on hf hd hcut,
    adjust_creates_tight_edge matrix rows columns selectedRows selectedColumns delta pair.1 pair.2 hp.1.1 hp.1.2 rfl⟩

omit [DecidableEq A] in
/-- Sparse weak duality bounds the objective using only allowed-edge costs and
one compatible perfect assignment; forbidden pairs need no numeric sentinel. -/
theorem dualValue_le_card_mul_on {edges : A → A → Prop} {matrix : A → A → K} {rows columns : A → K}
    (bound : K) (hf : FeasibleOn edges matrix rows columns)
    (hc : ∀ row column, edges row column → matrix row column ≤ bound)
    (he : ∃ assignment : Equiv.Perm A, Compatible edges assignment) :
    dualValue rows columns ≤ (Fintype.card A : K)*bound := by
  obtain ⟨assignment,hAssignment⟩ := he
  apply (weak_duality_on hf assignment hAssignment).trans
  unfold cost
  calc
    _ ≤ ∑ _ : A, bound := Finset.sum_le_sum (fun row _ => hc row (assignment row) (hAssignment row))
    _ = _ := by simp

omit [DecidableEq A] in
/-- The total feasible dual increment stays within the same dimension/cost
budget in a sparse graph. This supports checked machine arithmetic before any
actual cut update is executed. -/
theorem total_increment_bound_on {edges : A → A → Prop} {matrix : A → A → K}
    (initialRows finalRows finalColumns : A → K) (bound increment : K)
    (hlower : ∀ row, -bound ≤ initialRows row)
    (hupper : ∀ row column, edges row column → matrix row column ≤ bound)
    (hf : FeasibleOn edges matrix finalRows finalColumns)
    (he : ∃ assignment : Equiv.Perm A, Compatible edges assignment)
    (hvalue : dualValue finalRows finalColumns = dualValue initialRows (fun _ => 0)+increment) :
    increment ≤ 2*(Fintype.card A : K)*bound := by
  have hfinal := dualValue_le_card_mul_on bound hf hupper he
  have hstart : -(Fintype.card A : K)*bound ≤ dualValue initialRows (fun _ => 0) := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset A)) (fun row _ => hlower row)
    simpa only [dualValue,Finset.sum_const_zero,add_zero,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_neg,neg_mul] using hh
  linarith

/-- The ideal sparse cut update obeys its next numeric envelope before the
machine additions are required to fit. Existing tight-edge preservation and
one-excess-row objective accounting apply without adding forbidden edges. -/
theorem ideal_adjustment_increment_bound_on {edges : A → A → Prop} {matrix : A → A → K}
    (initialRows rows columns : A → K) (selectedRows selectedColumns : Finset A) (increment delta bound : K)
    (hlower : ∀ row, -bound ≤ initialRows row)
    (hupper : ∀ row column, edges row column → matrix row column ≤ bound)
    (hf : FeasibleOn edges matrix rows columns) (hd : 0 ≤ delta)
    (hcut : ∀ row ∈ selectedRows, ∀ column, column ∉ selectedColumns → edges row column →
      delta ≤ matrix row column-rows row-columns column)
    (hcard : selectedRows.card = selectedColumns.card+1)
    (he : ∃ assignment : Equiv.Perm A, Compatible edges assignment)
    (haccount : dualValue rows columns = dualValue initialRows (fun _ => 0)+increment) :
    increment+delta ≤ 2*(Fintype.card A : K)*bound := by
  apply total_increment_bound_on initialRows (adjustRows rows selectedRows delta) (adjustColumns columns selectedColumns delta)
    bound (increment+delta) hlower hupper (adjust_feasible_on hf hd hcut) he
  rw [adjust_dualValue_one rows columns selectedRows selectedColumns delta hcard,haccount]
  ring

end SubtreeProofs.Assignment

end
