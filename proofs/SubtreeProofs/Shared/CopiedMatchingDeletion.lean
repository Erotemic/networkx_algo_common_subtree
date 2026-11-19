module

public import SubtreeProofs.Shared.CopiedAssignmentReduction
public import SubtreeProofs.Shared.AssignmentVertexDeletion
import Mathlib.Tactic

/-!
# The one-pair deletion deficit in the paper's copied graph

A matched original right vertex and its copy occupy one column and one row.
Their deletion retains a compatible partial matching with exactly one missing
edge. The unique free endpoints and tightness of every retained edge are
identified directly from the original perfect assignment. This supplies the
combinatorial input to the later one-augmentation repair, without presuming
that the repair algorithm or its cost has already been verified.
-/

@[expose] public section

namespace SubtreeProofs.WeightedMatching.CopiedAssignmentReduction

variable {L R K : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Optional costs represent exactly allowed source edges; absent edges stay
absent and are never assigned an artificial finite cost. -/
noncomputable def edgeWeight (weights : L → R → Option K) (row column : L ⊕ R) : Option K := by
  classical
  exact if Allowed weights row column then some (profit weights row column) else none

/-- A retained original edge has precisely its original nonnegative weight. -/
theorem original_edge_weight (weights : L → R → Option K) (left : L) (right : R) (value : K)
    (he : weights left right = some value) (hn : 0 ≤ value) :
    edgeWeight weights (.inl left) (.inr right) = some value := by
  simp only [edgeWeight,Allowed,he,reduceCtorEq,ne_eq,not_false_eq_true,Option.getD_some,true_and,hn,↓reduceIte,
    profit,AssignmentReduction.profit,max_eq_right hn,add_zero]

/-- Its reversed copy receives the same weight, not a second edge convention. -/
theorem copy_edge_weight (weights : L → R → Option K) (left : L) (right : R) (value : K)
    (he : weights left right = some value) (hn : 0 ≤ value) :
    edgeWeight weights (.inr right) (.inl left) = some value := by
  simp only [edgeWeight,Allowed,he,reduceCtorEq,ne_eq,not_false_eq_true,Option.getD_some,true_and,hn,↓reduceIte,
    profit,AssignmentReduction.profit,max_eq_right hn,zero_add]

theorem identity_edge_weight (weights : L → R → Option K) (vertex : L ⊕ R) :
    edgeWeight weights vertex vertex = some 0 := by
  cases vertex <;> simp only [edgeWeight,Allowed,↓reduceIte,profit,AssignmentReduction.profit,add_zero]

/-- Exact compatibility of the perfect source assignment in the optional
copied graph follows from its independent allowed-edge predicate. -/
theorem allowed_edgeWeight (weights : L → R → Option K) (assignment : Equiv.Perm (L ⊕ R))
    (h : AllowedAssignment weights assignment) : ∀ row, edgeWeight weights row (assignment row) ≠ none := by
  intro row
  simp only [edgeWeight,h row,↓reduceIte,ne_eq,reduceCtorEq,not_false_eq_true]

/-- A positive decoded original edge at the removed right vertex forces its
copy row and original column to belong to different old assignment edges. -/
theorem matched_unpaired (weights : L → R → Option K) (assignment : Equiv.Perm (L ⊕ R)) (removed : R)
    (hmatched : ∃ left, (left,removed) ∈ AssignmentReduction.decode weights assignment) :
    assignment (.inr removed) ≠ .inr removed := by
  obtain ⟨left,hleft⟩ := hmatched
  have he := ((AssignmentReduction.mem_decode weights assignment (left,removed)).mp hleft).1
  intro hfixed
  have hsame := assignment.injective (he.trans hfixed.symm)
  cases hsame

/-- Removing the matched vertex and its copy leaves exactly one free pair in
an independently valid matching on the induced graph, with exact endpoints. -/
theorem matched_deletion_ready (weights : L → R → Option K) (assignment : Equiv.Perm (L ⊕ R)) (removed : R)
    (hallowed : AllowedAssignment weights assignment)
    (hmatched : ∃ left, (left,removed) ∈ AssignmentReduction.decode weights assignment) :
    ∃ freeRow freeColumn : L ⊕ R,
      freeRow ≠ .inr removed ∧ freeColumn ≠ .inr removed ∧
      (AssignmentVertexDeletion.remainingPairs assignment (.inr removed) (.inr removed)).card+1 = Fintype.card L+Fintype.card R-1 ∧
      (∀ row, row ≠ .inr removed →
        ((¬ ∃ column, (row,column) ∈ AssignmentVertexDeletion.remainingPairs assignment (.inr removed) (.inr removed)) ↔ row = freeRow)) ∧
      (∀ column, column ≠ .inr removed →
        ((¬ ∃ row, (row,column) ∈ AssignmentVertexDeletion.remainingPairs assignment (.inr removed) (.inr removed)) ↔ column = freeColumn)) ∧
      Valid (AssignmentVertexDeletion.deleteEndpoints (edgeWeight weights) (.inr removed) (.inr removed))
        (AssignmentVertexDeletion.remainingPairs assignment (.inr removed) (.inr removed)) := by
  classical
  have hu := matched_unpaired weights assignment removed hmatched
  refine ⟨assignment.symm (.inr removed),assignment (.inr removed),?_,hu,?_,?_,?_,?_⟩
  · intro he
    apply hu
    have hv := congrArg assignment he
    simpa only [Equiv.apply_symm_apply] using hv.symm
  · simpa only [Fintype.card_sum] using AssignmentVertexDeletion.one_pair_deficit assignment (.inr removed) (.inr removed) hu
  · exact fun row hr => AssignmentVertexDeletion.row_unmatched_iff assignment (.inr removed) (.inr removed) row hr
  · exact fun column hc => AssignmentVertexDeletion.column_unmatched_iff assignment (.inr removed) (.inr removed) column hc
  · exact AssignmentVertexDeletion.remainingPairs_valid_deleted (edgeWeight weights) assignment (allowed_edgeWeight weights assignment hallowed) _ _

/-- Source complementary tightness is preserved by endpoint removal; no new
potentials or result certificate are silently introduced by the deletion. -/
theorem deletion_preserves_tight (weights : L → R → Option K) (assignment : Equiv.Perm (L ⊕ R))
    (rows columns : L ⊕ R → K)
    (htight : ∀ row, rows row + columns (assignment row) = profit weights row (assignment row)) (removed : R) :
    ∀ pair ∈ AssignmentVertexDeletion.remainingPairs assignment (.inr removed) (.inr removed),
      rows pair.1 + columns pair.2 = profit weights pair.1 pair.2 := by
  classical
  exact AssignmentVertexDeletion.remainingPairs_tight (profit weights) rows columns assignment htight _ _

end SubtreeProofs.WeightedMatching.CopiedAssignmentReduction

end
