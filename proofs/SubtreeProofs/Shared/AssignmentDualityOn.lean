module

public import SubtreeProofs.Shared.AssignmentDuality
import Mathlib.Tactic

/-!
# Assignment duality with forbidden edges

Feasible dual inequalities apply only to actual edges. Perfect assignments
must respect that independent edge relation. This supports sparse copied
graphs without replacing forbidden pairs by a finite cost. Sum/permutation
arguments reuse the complete assignment objective and dual sum definitions.
-/

@[expose] public section

namespace SubtreeProofs.Assignment

variable {A K : Type*} [Fintype A] [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

def Compatible (edges : A → A → Prop) (assignment : Equiv.Perm A) : Prop :=
  ∀ row, edges row (assignment row)

def FeasibleOn (edges : A → A → Prop) (matrix : A → A → K) (rows columns : A → K) : Prop :=
  ∀ row column, edges row column → rows row + columns column ≤ matrix row column

def IsMinimumOn (edges : A → A → Prop) (matrix : A → A → K) (assignment : Equiv.Perm A) : Prop :=
  Compatible edges assignment ∧ ∀ other, Compatible edges other → cost matrix assignment ≤ cost matrix other

/-- Every compatible perfect assignment is bounded by every feasible dual. -/
theorem weak_duality_on {edges : A → A → Prop} {matrix : A → A → K} {rows columns : A → K}
    (h : FeasibleOn edges matrix rows columns) (assignment : Equiv.Perm A) (hc : Compatible edges assignment) :
    dualValue rows columns ≤ cost matrix assignment := by
  rw [dualValue_eq_sum rows columns assignment]
  exact Finset.sum_le_sum (fun row _ => h row (assignment row) (hc row))

/-- Feasible/tight compatible assignment is independently minimum among all
compatible perfect assignments of the sparse graph. -/
theorem isMinimumOn_of_feasible_tight {edges : A → A → Prop} {matrix : A → A → K} {rows columns : A → K}
    {assignment : Equiv.Perm A} (hfeasible : FeasibleOn edges matrix rows columns)
    (hcompatible : Compatible edges assignment) (htight : Tight matrix rows columns assignment) :
    IsMinimumOn edges matrix assignment := by
  refine ⟨hcompatible,?_⟩
  intro other hother
  rw [cost_eq_dual htight]
  exact weak_duality_on hfeasible other hother

/-- Equality of the independently computed primal and dual sums forces every
selected compatible edge tight; all reduced-cost slacks are nonnegative. -/
theorem tight_of_cost_eq_dual_on {edges : A → A → Prop} {matrix : A → A → K} {rows columns : A → K}
    {assignment : Equiv.Perm A} (hfeasible : FeasibleOn edges matrix rows columns)
    (hcompatible : Compatible edges assignment) (hequal : cost matrix assignment = dualValue rows columns) :
    Tight matrix rows columns assignment := by
  have hnonnegative : ∀ row, 0 ≤ matrix row (assignment row)-(rows row+columns (assignment row)) := by
    intro row
    exact sub_nonneg.mpr (hfeasible row (assignment row) (hcompatible row))
  have hsum : ∑ row, (matrix row (assignment row)-(rows row+columns (assignment row))) = 0 := by
    rw [Finset.sum_sub_distrib,← dualValue_eq_sum rows columns assignment]
    exact sub_eq_zero.mpr hequal
  intro row
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun entry _ => hnonnegative entry)).mp hsum row (Finset.mem_univ _)
  exact (sub_eq_zero.mp hz).symm

/-- Any equal-cost compatible replacement of a tight optimum stays tight under
the same dual. This justifies source matching normalization before deletions. -/
theorem tight_transfer_on {edges : A → A → Prop} {matrix : A → A → K} {rows columns : A → K}
    {first second : Equiv.Perm A} (hfeasible : FeasibleOn edges matrix rows columns)
    (hfirst : Tight matrix rows columns first) (hsecond : Compatible edges second)
    (hequal : cost matrix second = cost matrix first) : Tight matrix rows columns second := by
  apply tight_of_cost_eq_dual_on hfeasible hsecond
  exact hequal.trans (cost_eq_dual hfirst)

end SubtreeProofs.Assignment

end
