module

public import SubtreeProofs.Rust.AssignmentCostReconstruction
public import SubtreeProofs.Rust.AssignmentPotentialInitialization
import Mathlib.Tactic

/-!
# Actual complete assignment reconstruction and independent optimum

The two verified source loops invert a complete row-pointer matching, sum the
selected costs without overflow, and copy exact real potentials. Feasibility
and matched-edge tightness imply global optimality of the returned permutation.
The search/driver must still establish these input invariants.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentReconstruction

open AssignmentInitialization AssignmentInverseReconstruction AssignmentCostReconstruction

/-- Independent zero-based integer matrix on the represented real indices. -/
def matrix (cost : Slice (alloc.vec.Vec I64)) (n : Usize) (row col : Fin n.val) : ℤ :=
  (cost.val[row.val]!).val[col.val]!.val

def potential (values : Slice I128) (n : Usize) (index : Fin n.val) : ℤ :=
  values.val[index.val+1]!.val

/-- One-based version used by the independent row-pointer matching invariant. -/
def pointerMatrix (cost : Slice (alloc.vec.Vec I64)) (row col : Nat) : ℤ :=
  (cost.val[row-1]!).val[col-1]!.val

def Decoded (n : Usize) (assignment : Equiv.Perm (Fin n.val)) (columns : alloc.vec.Vec Usize) : Prop :=
  columns.length = n.val ∧ ∀ row : Fin n.val, columns.val[row.val]!.val = (assignment row).val

def Represents (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128) (n : Usize)
    (assignment : Equiv.Perm (Fin n.val)) (result : verified_assignment_core.Assignment) : Prop :=
  Decoded n assignment result.column_for_row ∧ result.row_potential.val = potentialPrefix u n.val ∧
    result.column_potential.val = potentialPrefix v n.val ∧ result.cost.val = SubtreeProofs.Assignment.cost (matrix cost n) assignment

structure InputBounds (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128) (matched : Slice Usize) (n : Usize) : Prop where
  n_max : n.val < Usize.max
  n_size : n.val ≤ U32.max
  cost_len : cost.length = n.val
  square : ∀ row < n.val, (cost.val[row]!).length = n.val
  matched_len : n.val < matched.length
  u_len : n.val < u.length
  v_len : n.val < v.length

theorem inversePrefix_decoded (n : Usize) (assignment : Equiv.Perm (Fin n.val)) (columns : alloc.vec.Vec Usize)
    (hprefix : InversePrefix n assignment columns (n.val+1)) : Decoded n assignment columns := by
  refine ⟨hprefix.1,?_⟩
  intro row
  have hbound : (assignment row).val+1 < n.val+1 := by have h := (assignment row).isLt; omega
  simpa only [ite_eq_left hbound] using hprefix.2 row

theorem prefixCost_eq_cost (cost : Slice (alloc.vec.Vec I64)) (n : Usize)
    (assignment : Equiv.Perm (Fin n.val)) (columns : alloc.vec.Vec Usize) (hdecoded : Decoded n assignment columns) :
    prefixCost cost columns n.val = SubtreeProofs.Assignment.cost (matrix cost n) assignment := by
  unfold prefixCost SubtreeProofs.Assignment.cost
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro row _
  unfold inputAt matrix
  rw [hdecoded.2 row]

/-- The actual complete reconstruction succeeds and returns the independent
inverse permutation, exact total cost, and precise copied potentials. -/
theorem reconstruct_assignment_spec (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128)
    (matched : Slice Usize) (n : Usize) (bounds : InputBounds cost u v matched n)
    (assignment : Equiv.Perm (Fin n.val)) (hinverse : ∀ row, matched.val[(assignment row).val+1]!.val = row.val+1) :
    reconstruct_assignment cost u v matched n ⦃ output => ∃ result,
      output = core.result.Result.Ok result ∧ Represents cost u v n assignment result ⦄ := by
  unfold reconstruct_assignment
  apply WP.spec_bind (zeros_usize_spec n)
  intro columns hcolumns
  apply WP.spec_bind (reconstruct_inverse_loop_spec matched n columns assignment hinverse bounds.matched_len bounds.n_max hcolumns)
  rintro ⟨failure,decoded⟩ ⟨hfailure,hprefix⟩
  dsimp only at hfailure hprefix ⊢
  subst failure
  simp only [uncurry_apply_pair]
  have hdecoded := inversePrefix_decoded n assignment decoded hprefix
  have costBounds : Bounds cost u v decoded n := by
    refine ⟨bounds.n_max,bounds.n_size,bounds.cost_len,bounds.square,hdecoded.1,?_,bounds.u_len,bounds.v_len⟩
    intro row hr
    have hd := hdecoded.2 ⟨row,hr⟩
    rw [hd]
    exact (assignment ⟨row,hr⟩).isLt
  apply WP.spec_bind (reconstruct_cost_loop_spec cost u v decoded n costBounds)
  rintro ⟨failure,total,rowPot,colPot⟩ ⟨hfailure,htotal,hrows,hcols⟩
  dsimp only at hfailure htotal hrows hcols ⊢
  subst failure
  simp only [uncurry_apply_pair,WP.spec_ok]
  exact ⟨_,rfl,hdecoded,hrows,hcols,htotal.trans (prefixCost_eq_cost cost n assignment decoded hdecoded)⟩

/-- Complete independent pointer matching, feasible dual potentials and tight
matched edges imply an actual successfully reconstructed global minimum.
This endpoint does not assume a minimum or a program correctness certificate. -/
theorem reconstruct_assignment_minimum_spec (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128)
    (matched : Slice Usize) (n : Usize) (bounds : InputBounds cost u v matched n)
    (hpartial : SubtreeProofs.Assignment.PartialRows n.val n.val (fun col => matched.val[col]!.val))
    (hfeasible : SubtreeProofs.Assignment.Feasible (matrix cost n) (potential u n) (potential v n))
    (htight : SubtreeProofs.Assignment.TightPointers n.val (pointerMatrix cost)
      (fun row => u.val[row]!.val) (fun col => v.val[col]!.val) (fun col => matched.val[col]!.val)) :
    reconstruct_assignment cost u v matched n ⦃ output => ∃ result, ∃ assignment : Equiv.Perm (Fin n.val),
      output = core.result.Result.Ok result ∧ Represents cost u v n assignment result ∧
        result.cost.val = SubtreeProofs.Assignment.dualValue (potential u n) (potential v n) ∧
        ∀ other, result.cost.val ≤ SubtreeProofs.Assignment.cost (matrix cost n) other ⦄ := by
  obtain ⟨assignment,hinverse⟩ := hpartial.exists_permutation
  have hassignment : SubtreeProofs.Assignment.Tight (matrix cost n) (potential u n) (potential v n) assignment := by
    have ht := SubtreeProofs.Assignment.tight_of_inverse (pointerMatrix cost)
      (fun row => u.val[row]!.val) (fun col => v.val[col]!.val) (fun col => matched.val[col]!.val) assignment hinverse htight
    intro row
    change u.val[row.val+1]!.val + v.val[(assignment row).val+1]!.val = (cost.val[row.val]!).val[(assignment row).val]!.val
    simpa only [pointerMatrix,Nat.add_sub_cancel] using ht row
  apply WP.spec_mono (reconstruct_assignment_spec cost u v matched n bounds assignment hinverse)
  rintro output ⟨result,houtput,hrep⟩
  refine ⟨result,assignment,houtput,hrep,?_,?_⟩
  · exact hrep.2.2.2.trans (SubtreeProofs.Assignment.cost_eq_dual hassignment)
  · intro other
    rw [hrep.2.2.2]
    exact SubtreeProofs.Assignment.tight_feasible_minimum hfeasible hassignment other

end SubtreeProofs.Rust.AssignmentReconstruction

end
