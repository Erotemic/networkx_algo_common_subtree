module

public import SubtreeProofs.Shared.AssignmentDualityOn
public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic

/-! # A single alternating-cycle repair suffices for a tight one-edge deficit -/

@[expose] public section

namespace SubtreeProofs.Assignment

variable {A K : Type*} [Fintype A] [DecidableEq A]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Replace just the permutation cycle containing the free row. Completing a
near-perfect matching by its free row/column gives the first permutation;
removing that dummy edge from this cycle leaves one alternating repair path. -/
noncomputable def cyclePatch (original replacement : Equiv.Perm A) (root : A) : Equiv.Perm A := by
  classical
  exact original * (original⁻¹*replacement).cycleOf root

/-- A cycle patch uses replacement edges on the chosen alternating cycle and
leaves every other old matching edge unchanged. -/
theorem cyclePatch_apply (original replacement : Equiv.Perm A) (root row : A) :
    cyclePatch original replacement root row =
      if (original⁻¹*replacement).SameCycle root row then replacement row else original row := by
  classical
  rw [cyclePatch,Equiv.Perm.mul_apply,Equiv.Perm.cycleOf_apply]
  split
  · simp only [Equiv.Perm.mul_apply]
    exact original.apply_symm_apply (replacement row)
  · rfl

/-- The free row always receives its replacement edge, including a one-edge
repair whose difference permutation fixes that row. -/
theorem cyclePatch_root (original replacement : Equiv.Perm A) (root : A) :
    cyclePatch original replacement root root = replacement root := by
  classical
  rw [cyclePatch_apply,ite_eq_left Equiv.Perm.SameCycle.rfl]

/-- Actual allowed edges remain allowed when only one old edge may be missing. -/
theorem cyclePatch_compatible (edges : A → A → Prop) (original replacement : Equiv.Perm A) (root : A)
    (ho : ∀ row, row ≠ root → edges row (original row)) (hr : Compatible edges replacement) :
    Compatible edges (cyclePatch original replacement root) := by
  classical
  intro row
  rw [cyclePatch_apply]
  split
  · exact hr row
  · rename_i hn
    apply ho row
    intro he
    subst row
    exact hn Equiv.Perm.SameCycle.rfl

omit [DecidableEq A] [LinearOrder K] [IsStrictOrderedRing K] in
/-- The sum of all assignment slacks is its primal cost minus the common dual
objective, for any permutation, whether or not its edges are allowed. -/
theorem slack_sum (matrix : A → A → K) (rows columns : A → K) (assignment : Equiv.Perm A) :
    (∑ row, (matrix row (assignment row)-(rows row+columns (assignment row)))) =
      cost matrix assignment-dualValue rows columns := by
  rw [Finset.sum_sub_distrib,dualValue_eq_sum rows columns assignment]
  rfl

/-- Patching the free-row cycle costs no more than any compatible replacement:
all omitted replacement cycles replace old tight edges by nonnegative slack. -/
theorem cyclePatch_cost_le (edges : A → A → Prop) (matrix : A → A → K) (rows columns : A → K)
    (original replacement : Equiv.Perm A) (root : A)
    (hf : FeasibleOn edges matrix rows columns)
    (ht : ∀ row, row ≠ root → rows row+columns (original row) = matrix row (original row))
    (hr : Compatible edges replacement) :
    cost matrix (cyclePatch original replacement root) ≤ cost matrix replacement := by
  classical
  have hslack : ∀ row,
      matrix row (cyclePatch original replacement root row)-(rows row+columns (cyclePatch original replacement root row)) ≤
      matrix row (replacement row)-(rows row+columns (replacement row)) := by
    intro row
    rw [cyclePatch_apply]
    split
    · exact le_refl _
    · rename_i hn
      have hne : row ≠ root := by
        intro he
        subst row
        exact hn Equiv.Perm.SameCycle.rfl
      have hh := ht row hne
      have hb := hf row (replacement row) (hr row)
      linarith
  have hs := Finset.sum_le_sum (fun row (_ : row ∈ (Finset.univ : Finset A)) => hslack row)
  rw [slack_sum,slack_sum] at hs
  linarith

/-- Every optimal compatible assignment can be replaced by an equally optimal
single-cycle repair of the tight near-perfect matching. -/
theorem cyclePatch_isMinimum (edges : A → A → Prop) (matrix : A → A → K) (rows columns : A → K)
    (original replacement : Equiv.Perm A) (root : A)
    (hf : FeasibleOn edges matrix rows columns)
    (ho : ∀ row, row ≠ root → edges row (original row))
    (ht : ∀ row, row ≠ root → rows row+columns (original row) = matrix row (original row))
    (hr : IsMinimumOn edges matrix replacement) :
    IsMinimumOn edges matrix (cyclePatch original replacement root) := by
  refine ⟨cyclePatch_compatible edges original replacement root ho hr.1,?_⟩
  intro other he
  exact (cyclePatch_cost_le edges matrix rows columns original replacement root hf ht hr.1).trans (hr.2 other he)

omit [DecidableEq A] [IsStrictOrderedRing K] in
/-- Finite compatible perfect assignments have an independent minimum whenever
at least one exists. This is an existence result, not a repair algorithm. -/
theorem exists_isMinimumOn (edges : A → A → Prop) (matrix : A → A → K)
    (he : ∃ assignment : Equiv.Perm A, Compatible edges assignment) : ∃ assignment, IsMinimumOn edges matrix assignment := by
  classical
  obtain ⟨assignment,hCompatible,hMinimum⟩ := Set.exists_min_image {assignment : Equiv.Perm A | Compatible edges assignment}
    (cost matrix) (Set.toFinite _) he
  exact ⟨assignment,hCompatible,hMinimum⟩

/-- A feasible dual and tight old edges except at one free row admit an optimal
repair changing only one alternating cycle of a completed assignment. No optimal
replacement is supplied as an endpoint hypothesis. -/
theorem exists_single_cycle_repair (edges : A → A → Prop) (matrix : A → A → K) (rows columns : A → K)
    (original : Equiv.Perm A) (root : A)
    (hf : FeasibleOn edges matrix rows columns)
    (ho : ∀ row, row ≠ root → edges row (original row))
    (ht : ∀ row, row ≠ root → rows row+columns (original row) = matrix row (original row))
    (he : ∃ assignment : Equiv.Perm A, Compatible edges assignment) :
    ∃ replacement : Equiv.Perm A,
      IsMinimumOn edges matrix (cyclePatch original replacement root) ∧
      ∀ row, ¬ (original⁻¹*replacement).SameCycle root row → cyclePatch original replacement root row = original row := by
  classical
  obtain ⟨replacement,hMinimum⟩ := exists_isMinimumOn edges matrix he
  refine ⟨replacement,cyclePatch_isMinimum edges matrix rows columns original replacement root hf ho ht hMinimum,?_⟩
  intro row hn
  rw [cyclePatch_apply,ite_eq_right hn]

end SubtreeProofs.Assignment

end
