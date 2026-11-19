module

public import SubtreeProofs.Shared.CopiedMatchingDuality
public import SubtreeProofs.Shared.AssignmentDeletedPermutation
import Mathlib.Tactic

/-! # Single-cycle optimal repair of the actual 2016 copied graph after deletion -/

@[expose] public section

namespace SubtreeProofs.WeightedMatching.CopiedAssignmentReduction

variable {L R K : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A matched original right vertex and its copy can be deleted and repaired
optimally by changing one alternating cycle of the completed surviving
assignment. Every other old edge remains unchanged. Feasibility is constructed
from the actual surviving identity-copy edges, not supplied as an optimum or
path certificate. Negative profit is only the minimization convention. -/
theorem matched_single_cycle_repair (weights : L → R → Option K) (assignment : Equiv.Perm (L ⊕ R)) (removed : R)
    (rows columns : L ⊕ R → K) (hfeasible : DualFeasible weights rows columns)
    (hallowed : AllowedAssignment weights assignment) (htight : DualTight weights rows columns assignment)
    (hmatched : ∃ left, (left,removed) ∈ AssignmentReduction.decode weights assignment) :
    let completed := AssignmentVertexDeletion.onRemaining assignment (.inr removed)
    let free := AssignmentVertexDeletion.freeRow assignment (.inr removed) (matched_unpaired weights assignment removed hmatched)
    ∃ replacement : Equiv.Perm { vertex : L ⊕ R // vertex ≠ .inr removed },
      Assignment.IsMinimumOn (fun row column => Allowed weights row.val column.val)
        (fun row column => -profit weights row.val column.val) (Assignment.cyclePatch completed replacement free) ∧
      ∀ row, ¬ (completed⁻¹*replacement).SameCycle free row →
        (Assignment.cyclePatch completed replacement free row).val = assignment row.val := by
  classical
  have hExists : ∃ replacement : Equiv.Perm { vertex : L ⊕ R // vertex ≠ .inr removed },
      Assignment.Compatible (fun row column => Allowed weights row.val column.val) replacement := by
    refine ⟨1,?_⟩
    intro vertex
    change Allowed weights vertex.val vertex.val
    cases vertex.val <;> rfl
  exact AssignmentVertexDeletion.exists_deleted_cycle_repair (Allowed weights) (fun row column => -profit weights row column)
    (fun row => -rows row) (fun column => -columns column) assignment (.inr removed)
    (matched_unpaired weights assignment removed hmatched) (negative_dual_feasible weights rows columns hfeasible)
    hallowed (negative_dual_tight weights rows columns assignment htight) hExists

end SubtreeProofs.WeightedMatching.CopiedAssignmentReduction

end
