module

public import SubtreeProofs.Shared.AssignmentDuality
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Rectangular complete injections and their dual certificates

Every row is assigned once; columns may be unused. Nonpositive column
potentials and zero potentials at unused columns are the additional
complementary-slackness conditions compared with square permutations.
The objective compares all injections into the full column type.
-/

@[expose] public section

namespace SubtreeProofs.Assignment

variable {A B K : Type*} [Fintype A] [Fintype B]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

def injectionCost (matrix : A → B → K) (assignment : A ↪ B) : K :=
  ∑ row, matrix row (assignment row)

def rectangularDualValue (rows : A → K) (columns : B → K) : K :=
  (∑ row, rows row) + ∑ column, columns column

def RectangularFeasible (matrix : A → B → K) (rows : A → K) (columns : B → K) : Prop :=
  ∀ row column, rows row + columns column ≤ matrix row column

def RectangularTight (matrix : A → B → K) (rows : A → K) (columns : B → K)
    (assignment : A ↪ B) : Prop :=
  ∀ row, rows row + columns (assignment row) = matrix row (assignment row)

def IsMinimumInjection (matrix : A → B → K) (assignment : A ↪ B) : Prop :=
  ∀ other : A ↪ B, injectionCost matrix assignment ≤ injectionCost matrix other

omit [Fintype B] [LinearOrder K] [IsStrictOrderedRing K] in
/-- The selected column sum counts each occupied original column once. -/
theorem sum_injection [DecidableEq B] (columns : B → K) (assignment : A ↪ B) :
    (∑ row, columns (assignment row)) = ∑ column ∈ Finset.univ.image assignment, columns column := by
  classical
  rw [Finset.sum_image (fun _ _ _ _ he => assignment.injective he)]

/-- Unused columns can only lower the dual objective, because their potentials
are nonpositive. This is weak duality for every full rectangular injection. -/
theorem rectangular_weak_duality {matrix : A → B → K} {rows : A → K} {columns : B → K}
    (hFeasible : RectangularFeasible matrix rows columns) (hColumns : ∀ column, columns column ≤ 0)
    (assignment : A ↪ B) : rectangularDualValue rows columns ≤ injectionCost matrix assignment := by
  classical
  have hsum : (∑ column, columns column) ≤ ∑ row, columns (assignment row) := by
    rw [sum_injection]
    exact Finset.sum_le_sum_of_subset_of_nonpos (Finset.subset_univ _) (fun column _ _ => hColumns column)
  unfold rectangularDualValue injectionCost
  calc
    _ ≤ (∑ row, rows row) + ∑ row, columns (assignment row) := by linarith
    _ = ∑ row, (rows row + columns (assignment row)) := Finset.sum_add_distrib.symm
    _ ≤ _ := Finset.sum_le_sum (fun row _ => hFeasible row (assignment row))

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Tight selected edges and zero unused columns attain the whole dual sum. -/
theorem injection_cost_eq_dual {matrix : A → B → K} {rows : A → K} {columns : B → K}
    {assignment : A ↪ B} (hTight : RectangularTight matrix rows columns assignment)
    (hUnused : ∀ column, (¬ ∃ row, assignment row = column) → columns column = 0) :
    injectionCost matrix assignment = rectangularDualValue rows columns := by
  classical
  have hsum : (∑ row, columns (assignment row)) = ∑ column, columns column := by
    rw [sum_injection]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro column _ hnot
    apply hUnused column
    rintro ⟨row,he⟩
    exact hnot (Finset.mem_image.mpr ⟨row,Finset.mem_univ _,he⟩)
  unfold injectionCost rectangularDualValue
  calc
    _ = ∑ row, (rows row + columns (assignment row)) := Finset.sum_congr rfl (fun row _ => (hTight row).symm)
    _ = (∑ row, rows row) + ∑ row, columns (assignment row) := Finset.sum_add_distrib
    _ = _ := by rw [hsum]

/-- A concrete rectangular primal/dual certificate proves optimality against
all original columns, not merely a preselected subset. -/
theorem minimum_injection_of_feasible_tight {matrix : A → B → K} {rows : A → K} {columns : B → K}
    {assignment : A ↪ B} (hFeasible : RectangularFeasible matrix rows columns)
    (hColumns : ∀ column, columns column ≤ 0) (hTight : RectangularTight matrix rows columns assignment)
    (hUnused : ∀ column, (¬ ∃ row, assignment row = column) → columns column = 0) :
    IsMinimumInjection matrix assignment := by
  intro other
  rw [injection_cost_eq_dual hTight hUnused]
  exact rectangular_weak_duality hFeasible hColumns other

end SubtreeProofs.Assignment

end
