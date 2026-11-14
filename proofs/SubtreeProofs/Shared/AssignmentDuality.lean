module

public import SubtreeProofs.Shared.AssignmentReduction
import Mathlib.Tactic

/-!
# Assignment optimality from dual potentials

This is the finite permutation form of the Hungarian primal/dual criterion.
It applies directly to both exact integer and real cost models. A feasible
potential and a tight complete assignment certify minimum total cost.
-/

@[expose] public section

namespace SubtreeProofs.Assignment

variable {A K : Type*} [Fintype A] [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

def cost (matrix : A → A → K) (assignment : Equiv.Perm A) : K := ∑ row, matrix row (assignment row)

def Feasible (matrix : A → A → K) (rows columns : A → K) : Prop :=
  ∀ row col, rows row + columns col ≤ matrix row col

def Tight (matrix : A → A → K) (rows columns : A → K) (assignment : Equiv.Perm A) : Prop :=
  ∀ row, rows row + columns (assignment row) = matrix row (assignment row)

def dualValue (rows columns : A → K) : K := (∑ row, rows row) + ∑ col, columns col

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Permuting columns leaves the sum of potentials unchanged. -/
theorem dualValue_eq_sum (rows columns : A → K) (assignment : Equiv.Perm A) :
    dualValue rows columns = ∑ row, (rows row + columns (assignment row)) := by
  rw [Finset.sum_add_distrib, Equiv.sum_comp assignment columns]
  rfl

/-- Every complete assignment costs at least every feasible dual objective. -/
theorem weak_duality {matrix : A → A → K} {rows columns : A → K}
    (h : Feasible matrix rows columns) (assignment : Equiv.Perm A) :
    dualValue rows columns ≤ cost matrix assignment := by
  rw [dualValue_eq_sum rows columns assignment]
  exact Finset.sum_le_sum (fun row _ => h row (assignment row))

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Complementary tightness is exact equality of primal and dual objectives. -/
theorem cost_eq_dual {matrix : A → A → K} {rows columns : A → K} {assignment : Equiv.Perm A}
    (h : Tight matrix rows columns assignment) : cost matrix assignment = dualValue rows columns := by
  rw [dualValue_eq_sum rows columns assignment]
  exact Finset.sum_congr rfl (fun row _ => (h row).symm)

/-- The optimality criterion maintained by an exact Hungarian implementation. -/
theorem tight_feasible_minimum {matrix : A → A → K} {rows columns : A → K} {assignment : Equiv.Perm A}
    (hfeasible : Feasible matrix rows columns) (htight : Tight matrix rows columns assignment) :
    ∀ other, cost matrix assignment ≤ cost matrix other := by
  intro other
  rw [cost_eq_dual htight]
  exact weak_duality hfeasible other

/-- Dummy assignment plus feasible/tight potentials certifies a globally
optimal compatible partial matching, including signed and forbidden weights. -/
theorem tight_assignment_decodes {L R : Type*} [Fintype L] [Fintype R]
    (weights : L → R → Option K) (shift : K) (rows columns : L ⊕ R → K)
    (assignment : Equiv.Perm (L ⊕ R))
    (hfeasible : Feasible (fun i j => shift - WeightedMatching.AssignmentReduction.profit weights i j) rows columns)
    (htight : Tight (fun i j => shift - WeightedMatching.AssignmentReduction.profit weights i j) rows columns assignment) :
    WeightedMatching.IsMaximum weights (WeightedMatching.AssignmentReduction.decode weights assignment) := by
  apply WeightedMatching.AssignmentReduction.minimum_assignment_decodes shift assignment
  exact tight_feasible_minimum hfeasible htight

end SubtreeProofs.Assignment

end
