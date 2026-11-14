module

public import SubtreeProofs.Shared.AssignmentCycleRepair
public import SubtreeProofs.Shared.AssignmentVertexDeletion
import Mathlib.Tactic

/-! # Completing the one-edge deficit after deleting an assignment vertex -/

@[expose] public section

namespace SubtreeProofs.AssignmentVertexDeletion

variable {A : Type*} [DecidableEq A]

/-- Bypass the deleted vertex in its permutation cycle. This fixes that vertex
and temporarily pairs the unique free row with the unique free column. -/
def bypass (assignment : Equiv.Perm A) (removed : A) : Equiv.Perm A :=
  assignment * Equiv.swap removed (assignment.symm removed)

@[simp] theorem bypass_removed (assignment : Equiv.Perm A) (removed : A) : bypass assignment removed removed = removed := by
  simp only [bypass,Equiv.Perm.mul_apply,Equiv.swap_apply_left,Equiv.apply_symm_apply]

@[simp] theorem bypass_free (assignment : Equiv.Perm A) (removed : A) :
    bypass assignment removed (assignment.symm removed) = assignment removed := by
  simp only [bypass,Equiv.Perm.mul_apply,Equiv.swap_apply_right]

theorem bypass_away (assignment : Equiv.Perm A) (removed row : A) (hr : row ≠ removed) (hf : row ≠ assignment.symm removed) :
    bypass assignment removed row = assignment row := by
  rw [bypass,Equiv.Perm.mul_apply,Equiv.swap_apply_def,ite_eq_right hr,ite_eq_right hf]

theorem bypass_nonremoved (assignment : Equiv.Perm A) (removed row : A) :
    bypass assignment removed row ≠ removed ↔ row ≠ removed := by
  constructor
  · intro hn he
    exact hn (he ▸ bypass_removed assignment removed)
  · intro hn he
    exact hn ((bypass assignment removed).injective (he.trans (bypass_removed assignment removed).symm))

/-- The completed surviving assignment acts only on actual undeleted vertices.
Its only possible non-source edge joins the two previously unmatched endpoints. -/
def onRemaining (assignment : Equiv.Perm A) (removed : A) : Equiv.Perm { row : A // row ≠ removed } :=
  (bypass assignment removed).subtypePerm (bypass_nonremoved assignment removed)

@[simp] theorem onRemaining_value (assignment : Equiv.Perm A) (removed : A) (row : { row : A // row ≠ removed }) :
    (onRemaining assignment removed row).val = bypass assignment removed row.val := rfl

theorem onRemaining_away (assignment : Equiv.Perm A) (removed : A) (row : { row : A // row ≠ removed })
    (hf : row.val ≠ assignment.symm removed) : (onRemaining assignment removed row).val = assignment row.val := by
  rw [onRemaining_value,bypass_away assignment removed row.val row.property hf]

omit [DecidableEq A] in
theorem free_row_survives (assignment : Equiv.Perm A) (removed : A) (hn : assignment removed ≠ removed) :
    assignment.symm removed ≠ removed := by
  intro he
  have hh := congrArg assignment he
  rw [Equiv.apply_symm_apply] at hh
  exact hn hh.symm

/-- The temporary completion has precisely the original free endpoints. -/
def freeRow (assignment : Equiv.Perm A) (removed : A) (hn : assignment removed ≠ removed) : { row : A // row ≠ removed } :=
  ⟨assignment.symm removed,free_row_survives assignment removed hn⟩

theorem onRemaining_free (assignment : Equiv.Perm A) (removed : A) (hn : assignment removed ≠ removed) :
    (onRemaining assignment removed (freeRow assignment removed hn)).val = assignment removed := by
  rw [onRemaining_value]
  exact bypass_free assignment removed

variable {K : Type*} [Fintype A] [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A compatible tight old perfect assignment, after deletion of a nonfixed
vertex, admits an optimal single-cycle repair of exactly its surviving edges.
The existence hypothesis concerns only feasibility of the reduced graph. -/
theorem exists_deleted_cycle_repair (edges : A → A → Prop) (matrix : A → A → K) (rows columns : A → K)
    (assignment : Equiv.Perm A) (removed : A) (hn : assignment removed ≠ removed)
    (hf : Assignment.FeasibleOn edges matrix rows columns) (hc : Assignment.Compatible edges assignment)
    (ht : Assignment.Tight matrix rows columns assignment)
    (he : ∃ replacement : Equiv.Perm { row : A // row ≠ removed },
      Assignment.Compatible (fun row column => edges row.val column.val) replacement) :
    ∃ replacement : Equiv.Perm { row : A // row ≠ removed },
      Assignment.IsMinimumOn (fun row column => edges row.val column.val) (fun row column => matrix row.val column.val)
        (Assignment.cyclePatch (onRemaining assignment removed) replacement (freeRow assignment removed hn)) ∧
      ∀ row, ¬ ((onRemaining assignment removed)⁻¹*replacement).SameCycle (freeRow assignment removed hn) row →
        (Assignment.cyclePatch (onRemaining assignment removed) replacement (freeRow assignment removed hn) row).val = assignment row.val := by
  classical
  have hAway : ∀ row : { row : A // row ≠ removed }, row ≠ freeRow assignment removed hn →
      (onRemaining assignment removed row).val = assignment row.val := by
    intro row hne
    apply onRemaining_away
    intro heq
    apply hne
    exact Subtype.ext heq
  have hFeasible : Assignment.FeasibleOn (fun row column : { row : A // row ≠ removed } => edges row.val column.val)
      (fun row column => matrix row.val column.val) (fun row => rows row.val) (fun column => columns column.val) := by
    intro row column hedge
    exact hf row.val column.val hedge
  obtain ⟨replacement,hMinimum,hUnchanged⟩ := Assignment.exists_single_cycle_repair
    (fun row column : { row : A // row ≠ removed } => edges row.val column.val)
    (fun row column => matrix row.val column.val) (fun row => rows row.val) (fun column => columns column.val)
    (onRemaining assignment removed) (freeRow assignment removed hn) hFeasible
    (by intro row hne; rw [hAway row hne]; exact hc row.val)
    (by intro row hne; rw [hAway row hne]; exact ht row.val) he
  refine ⟨replacement,hMinimum,?_⟩
  intro row hOutside
  have hne : row ≠ freeRow assignment removed hn := by
    intro heq
    subst row
    exact hOutside Equiv.Perm.SameCycle.rfl
  exact (congrArg Subtype.val (hUnchanged row hOutside)).trans (hAway row hne)

end SubtreeProofs.AssignmentVertexDeletion

end
