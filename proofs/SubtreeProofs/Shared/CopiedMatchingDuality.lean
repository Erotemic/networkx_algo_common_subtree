module

public import SubtreeProofs.Shared.AssignmentDualityOn
public import SubtreeProofs.Shared.CopiedMatchingInitialization
public import SubtreeProofs.Shared.MatchingDeletion
import Mathlib.Tactic

/-!
# Sparse copied-graph dual certificates and deletion-ready normalization

A compatible tight perfect assignment under a feasible source dual decodes to
an independently maximum original matching. Normalizing to the involution
that swaps just the decoded pairs preserves both weight and tightness under
the same dual, and fixes every unused vertex to its own copy. This makes the
matched/unmatched deletion split precise even if the old assignment used
zero-weight cross edges or had different original/copy matching components.
-/

@[expose] public section

namespace SubtreeProofs.WeightedMatching.CopiedAssignmentReduction

variable {L R K : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

def DualTight (weights : L → R → Option K) (rows columns : L ⊕ R → K) (assignment : Equiv.Perm (L ⊕ R)) : Prop :=
  ∀ row, rows row + columns (assignment row) = profit weights row (assignment row)

theorem negative_assignment_cost (weights : L → R → Option K) (assignment : Equiv.Perm (L ⊕ R)) :
    Assignment.cost (fun row column => -profit weights row column) assignment = -assignmentWeight weights assignment := by
  simp only [Assignment.cost,Finset.sum_neg_distrib,assignmentWeight]

theorem negative_dual_feasible (weights : L → R → Option K) (rows columns : L ⊕ R → K)
    (h : DualFeasible weights rows columns) :
    Assignment.FeasibleOn (Allowed weights) (fun row column => -profit weights row column)
      (fun row => -rows row) (fun column => -columns column) := by
  intro row column he
  have hb := h row column he
  linarith

theorem negative_dual_tight (weights : L → R → Option K) (rows columns : L ⊕ R → K) (assignment : Equiv.Perm (L ⊕ R))
    (h : DualTight weights rows columns assignment) :
    Assignment.Tight (fun row column => -profit weights row column) (fun row => -rows row) (fun column => -columns column) assignment := by
  intro row
  have he := h row
  linarith

/-- Source feasible/tight potentials certify maximal weight against every
allowed perfect assignment of the actual sparse copied graph. -/
theorem dominates_of_feasible_tight (weights : L → R → Option K) (assignment : Equiv.Perm (L ⊕ R))
    (rows columns : L ⊕ R → K) (hfeasible : DualFeasible weights rows columns)
    (hallowed : AllowedAssignment weights assignment) (htight : DualTight weights rows columns assignment) :
    ∀ other, AllowedAssignment weights other → assignmentWeight weights other ≤ assignmentWeight weights assignment := by
  have hm := Assignment.isMinimumOn_of_feasible_tight (negative_dual_feasible weights rows columns hfeasible)
    hallowed (negative_dual_tight weights rows columns assignment htight)
  intro other ho
  have hb := hm.2 other ho
  rw [negative_assignment_cost,negative_assignment_cost] at hb
  exact neg_le_neg_iff.mp hb

/-- The exact sparse source dual certificate yields independently maximum
original and copy matchings, with signed/forbidden weights and empty sides. -/
theorem feasible_tight_decodes (weights : L → R → Option K) (assignment : Equiv.Perm (L ⊕ R))
    (rows columns : L ⊕ R → K) (hfeasible : DualFeasible weights rows columns)
    (hallowed : AllowedAssignment weights assignment) (htight : DualTight weights rows columns assignment) :
    IsMaximum weights (AssignmentReduction.decode weights assignment) ∧
      IsMaximum weights (AssignmentReduction.decode weights assignment.symm) := by
  exact dominates_allowed_decodes weights assignment
    (dominates_of_feasible_tight weights assignment rows columns hfeasible hallowed htight)

/-- A perfect optimum can be normalized to matching-pair swaps under the same
feasible/tight dual. No recomputation of the optimum or potentials is needed.
Every unused right vertex then has its own copy edge, exactly as needed for
unmatched deletion reuse and the single-pair repair argument. -/
theorem normalize_tight (weights : L → R → Option K) (assignment : Equiv.Perm (L ⊕ R))
    (rows columns : L ⊕ R → K) (hfeasible : DualFeasible weights rows columns)
    (hallowed : AllowedAssignment weights assignment) (htight : DualTight weights rows columns assignment) :
    let pairs := AssignmentReduction.decode weights assignment
    let normalized := AssignmentReduction.extend (AssignmentReduction.decode_valid weights assignment)
    AllowedAssignment weights normalized ∧ DualTight weights rows columns normalized ∧
      assignmentWeight weights normalized = assignmentWeight weights assignment ∧
      ∀ right, right ∉ matchedRight pairs → normalized (.inr right) = .inr right := by
  let pairs := AssignmentReduction.decode weights assignment
  let hv := AssignmentReduction.decode_valid weights assignment
  let normalized := AssignmentReduction.extend hv
  change AllowedAssignment weights normalized ∧ DualTight weights rows columns normalized ∧
    assignmentWeight weights normalized = assignmentWeight weights assignment ∧
    ∀ right, right ∉ matchedRight pairs → normalized (.inr right) = .inr right
  have hm := feasible_tight_decodes weights assignment rows columns hfeasible hallowed htight
  have hn : AllowedAssignment weights normalized := extend_allowed hv hm.1.selected_nonnegative
  have hcomponent : weight weights (AssignmentReduction.decode weights assignment.symm) = weight weights pairs :=
    hm.2.weight_eq hm.1
  have hold : assignmentWeight weights assignment = 2 * weight weights pairs := by
    rw [assignmentWeight_decode,hcomponent]
    ring
  have hupper := dominates_of_feasible_tight weights assignment rows columns hfeasible hallowed htight normalized hn
  have hlower : 2 * weight weights pairs ≤ assignmentWeight weights normalized := weight_le_extend hv
  have hequal : assignmentWeight weights normalized = assignmentWeight weights assignment := by
    apply le_antisymm hupper
    rw [hold]
    exact hlower
  have hcost : Assignment.cost (fun row column => -profit weights row column) normalized =
      Assignment.cost (fun row column => -profit weights row column) assignment := by
    rw [negative_assignment_cost,negative_assignment_cost,hequal]
  have hnormalizedTight := Assignment.tight_transfer_on (negative_dual_feasible weights rows columns hfeasible)
    (negative_dual_tight weights rows columns assignment htight) hn hcost
  refine ⟨hn,?_,hequal,?_⟩
  · intro row
    have hb := hnormalizedTight row
    linarith
  · intro right hunused
    have hnone : AssignmentReduction.rightPartner pairs right = none := by
      cases he : AssignmentReduction.rightPartner pairs right with
      | none => rfl
      | some left =>
        have hp := (AssignmentReduction.rightPartner_some hv left right).mp he
        exact False.elim (hunused (Finset.mem_image.mpr ⟨(left,right),hp,rfl⟩))
    change AssignmentReduction.swapPartners pairs (.inr right) = .inr right
    simp only [AssignmentReduction.swapPartners,hnone]

end SubtreeProofs.WeightedMatching.CopiedAssignmentReduction

end
