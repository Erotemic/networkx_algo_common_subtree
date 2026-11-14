module

public import SubtreeProofs.Rust.AssignmentReconstruction
import Mathlib.Tactic

/-!
# Independent specification of the assignment returned by the public API

An actual output vector represents a finite permutation with its exact cost.
Its exported row/column potentials are feasible and tight, its primal and dual
objectives agree, and its cost is no greater than any competing permutation.
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace SubtreeProofs.Rust.AssignmentReturnedSpecification

open AssignmentCostReconstruction AssignmentReconstruction

def exportedPotential (values : alloc.vec.Vec I128) (n : Usize) (index : Fin n.val) : ℤ := values.val[index.val]!.val

/-- Independent optimum and dual properties of actual returned data. -/
def Correct (cost : Slice (alloc.vec.Vec I64)) (n : Usize) (result : verified_assignment_core.Assignment) : Prop :=
  ∃ assignment : Equiv.Perm (Fin n.val), Decoded n assignment result.column_for_row ∧
    result.row_potential.length = n.val ∧ result.column_potential.length = n.val ∧
    SubtreeProofs.Assignment.Feasible (matrix cost n) (exportedPotential result.row_potential n) (exportedPotential result.column_potential n) ∧
    SubtreeProofs.Assignment.Tight (matrix cost n) (exportedPotential result.row_potential n) (exportedPotential result.column_potential n) assignment ∧
    result.cost.val = SubtreeProofs.Assignment.cost (matrix cost n) assignment ∧
    result.cost.val = SubtreeProofs.Assignment.dualValue (exportedPotential result.row_potential n) (exportedPotential result.column_potential n) ∧
    ∀ other, result.cost.val ≤ SubtreeProofs.Assignment.cost (matrix cost n) other

theorem potentialPrefix_get (values : Slice I128) (count index : Nat) (hi : index < count) :
    (potentialPrefix values count)[index]! = values.val[index+1]! := by
  rw [getElem!_pos (potentialPrefix values count) index (by simpa only [potentialPrefix_length] using hi)]
  simp only [potentialPrefix,List.getElem_map,List.getElem_range]

theorem exportedPotential_eq (values : Slice I128) (copied : alloc.vec.Vec I128) (n : Usize)
    (hcopied : copied.val = potentialPrefix values n.val) : exportedPotential copied n = potential values n := by
  funext index
  unfold exportedPotential potential
  rw [hcopied,potentialPrefix_get values n.val index.val index.isLt]

/-- The actual decoder's exact data, independent feasibility and tightness
establish the full returned-data optimum specification. -/
theorem correct_of_represents (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128) (n : Usize)
    (assignment : Equiv.Perm (Fin n.val)) (result : verified_assignment_core.Assignment)
    (hrep : Represents cost u v n assignment result)
    (hfeasible : SubtreeProofs.Assignment.Feasible (matrix cost n) (potential u n) (potential v n))
    (htight : SubtreeProofs.Assignment.Tight (matrix cost n) (potential u n) (potential v n) assignment) : Correct cost n result := by
  have hr := exportedPotential_eq u result.row_potential n hrep.2.1
  have hc := exportedPotential_eq v result.column_potential n hrep.2.2.1
  refine ⟨assignment,hrep.1,?_,?_,?_,?_,hrep.2.2.2,?_,?_⟩
  · change result.row_potential.val.length = n.val
    rw [hrep.2.1,potentialPrefix_length]
  · change result.column_potential.val.length = n.val
    rw [hrep.2.2.1,potentialPrefix_length]
  · rw [hr,hc]
    exact hfeasible
  · rw [hr,hc]
    exact htight
  · rw [hr,hc,hrep.2.2.2]
    exact SubtreeProofs.Assignment.cost_eq_dual htight
  · intro other
    rw [hrep.2.2.2]
    exact SubtreeProofs.Assignment.tight_feasible_minimum hfeasible htight other

end SubtreeProofs.Rust.AssignmentReturnedSpecification

end
