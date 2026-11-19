module

public import SubtreeProofs.Shared.AssignmentReduction
import Mathlib.Tactic

/-!
# The copied-graph reduction of Droschinsky et al. 2016 Lemma 5

Rows are original left vertices and copies of right vertices. Columns are
copies of left vertices and original right vertices. Nonnegative compatible
original edges and their reversed copies retain their weight; only identity
edges connect a vertex with its own copy. Other edges are forbidden, rather
than represented by a finite negative sentinel.

The doubled assignment weight splits into independent original/copy matching
weights. A maximum over allowed perfect assignments therefore decodes to two
independently maximum partial matchings. This is a different reduction from
the dense zero-dummy adapter used by the current exact Rust reference solver.
-/

@[expose] public section

namespace SubtreeProofs.WeightedMatching

variable {L R K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Feasibility survives taking any subset of the selected pairs. -/
theorem Valid.subset {weights : L → R → Option K} {pairs other : Finset (L × R)}
    (h : Valid weights pairs) (hs : other ⊆ pairs) : Valid weights other := by
  exact ⟨fun p hp => h.1 p (hs hp),
    fun p hp q hq he => h.2.1 p (hs hp) q (hs hq) he,
    fun p hp q hq he => h.2.2 p (hs hp) q (hs hq) he⟩

/-- A maximum optional matching contains no negative edge: removing that
edge would otherwise strictly improve the independent objective. -/
theorem IsMaximum.selected_nonnegative {weights : L → R → Option K} {pairs : Finset (L × R)}
    (h : IsMaximum weights pairs) (pair : L × R) (hp : pair ∈ pairs) :
    0 ≤ (weights pair.1 pair.2).getD 0 := by
  classical
  have he := h.2 (pairs.erase pair) (h.1.subset (Finset.erase_subset _ _))
  have hsum : weight weights (pairs.erase pair) + (weights pair.1 pair.2).getD 0 = weight weights pairs := by
    exact Finset.sum_erase_add _ _ hp
  linarith

namespace CopiedAssignmentReduction

open AssignmentReduction

/-- Exactly the paper's nonnegative original/copy edges and zero identity
edges. Same-side off-diagonal pairs remain forbidden. -/
def Allowed (weights : L → R → Option K) : L ⊕ R → L ⊕ R → Prop
  | .inl left,.inl copy => left = copy
  | .inr copy,.inr right => copy = right
  | .inl left,.inr right => weights left right ≠ none ∧ 0 ≤ (weights left right).getD 0
  | .inr right,.inl left => weights left right ≠ none ∧ 0 ≤ (weights left right).getD 0

def AllowedAssignment (weights : L → R → Option K) (assignment : Equiv.Perm (L ⊕ R)) : Prop :=
  ∀ row, Allowed weights row (assignment row)

/-- Original and copied compatible edges receive the same clamped profit.
Feasibility is imposed separately by `Allowed`. -/
def profit (weights : L → R → Option K) (row column : L ⊕ R) : K :=
  AssignmentReduction.profit weights row column + AssignmentReduction.profit weights column row

variable [Fintype L] [Fintype R]

def assignmentWeight (weights : L → R → Option K) (assignment : Equiv.Perm (L ⊕ R)) : K :=
  ∑ row, profit weights row (assignment row)

/-- The copy contribution is the original contribution of the inverse
permutation. No graph symmetry or optimality assumption is needed. -/
theorem assignmentWeight_split (weights : L → R → Option K) (assignment : Equiv.Perm (L ⊕ R)) :
    assignmentWeight weights assignment = AssignmentReduction.assignmentWeight weights assignment +
      AssignmentReduction.assignmentWeight weights assignment.symm := by
  unfold assignmentWeight profit
  rw [Finset.sum_add_distrib]
  congr 1
  have he := Equiv.sum_comp assignment (fun column => AssignmentReduction.profit weights column (assignment.symm column))
  simpa only [Equiv.symm_apply_apply,AssignmentReduction.assignmentWeight] using he

/-- A feasible partial matching is extended by swapping every pair and fixing
unmatched vertices. It is an involution, so its copied profit is doubled. -/
theorem extend_symm {weights : L → R → Option K} {pairs : Finset (L × R)} (h : Valid weights pairs) :
    (extend h).symm = extend h := by
  apply Equiv.ext
  intro row
  apply (extend h).injective
  rw [Equiv.apply_symm_apply]
  exact (swapPartners_involutive h row).symm

/-- Nonnegative compatible partial matchings extend to perfect matchings on
exactly the sparse copied graph, including zero and unmatched edges. -/
theorem extend_allowed {weights : L → R → Option K} {pairs : Finset (L × R)} (h : Valid weights pairs)
    (hnonnegative : ∀ pair ∈ pairs, 0 ≤ (weights pair.1 pair.2).getD 0) : AllowedAssignment weights (extend h) := by
  intro row
  cases row with
  | inl left =>
    cases he : leftPartner pairs left with
    | none =>
      change Allowed weights (.inl left) (swapPartners pairs (.inl left))
      simp only [swapPartners,he,Allowed]
    | some right =>
      have hp := (leftPartner_some h left right).mp he
      change Allowed weights (.inl left) (swapPartners pairs (.inl left))
      simpa only [swapPartners,he,Allowed] using And.intro (h.1 _ hp) (hnonnegative _ hp)
  | inr right =>
    cases he : rightPartner pairs right with
    | none =>
      change Allowed weights (.inr right) (swapPartners pairs (.inr right))
      simp only [swapPartners,he,Allowed]
    | some left =>
      have hp := (rightPartner_some h left right).mp he
      change Allowed weights (.inr right) (swapPartners pairs (.inr right))
      simpa only [swapPartners,he,Allowed] using And.intro (h.1 _ hp) (hnonnegative _ hp)

theorem weight_le_extend {weights : L → R → Option K} {pairs : Finset (L × R)} (h : Valid weights pairs) :
    2 * weight weights pairs ≤ assignmentWeight weights (extend h) := by
  rw [assignmentWeight_split,extend_symm h]
  have hb := AssignmentReduction.weight_le_extend h
  linarith

/-- Every copied assignment's profit is exactly the sum of the two decoded
partial matchings, with no incompatible or negative pair included. -/
theorem assignmentWeight_decode (weights : L → R → Option K) (assignment : Equiv.Perm (L ⊕ R)) :
    assignmentWeight weights assignment = weight weights (decode weights assignment) + weight weights (decode weights assignment.symm) := by
  rw [assignmentWeight_split,decode_weight,decode_weight]

/-- The finite copied graph always has a perfect matching: the empty original
matching extends to the identity copy edges, even on empty bipartitions. -/
theorem exists_allowed_assignment (weights : L → R → Option K) :
    ∃ assignment : Equiv.Perm (L ⊕ R), AllowedAssignment weights assignment := by
  refine ⟨Equiv.refl _,?_⟩
  intro row
  cases row <;> rfl

/-- Dominating every allowed perfect assignment suffices to make both decoded
components independently maximum. In particular every maximum perfect
matching of the paper's copied graph returns the desired original optimum. -/
theorem dominates_allowed_decodes (weights : L → R → Option K) (assignment : Equiv.Perm (L ⊕ R))
    (hmax : ∀ other, AllowedAssignment weights other → assignmentWeight weights other ≤ assignmentWeight weights assignment) :
    IsMaximum weights (decode weights assignment) ∧ IsMaximum weights (decode weights assignment.symm) := by
  classical
  let best := exhaustive (Finset.univ : Finset (L × R)).toList weights
  have hbest : IsMaximum weights best := by
    apply exhaustive_correct
    intro pair
    exact Finset.mem_toList.mpr (Finset.mem_univ _)
  have hallowed := extend_allowed hbest.1 hbest.selected_nonnegative
  have hdominates := (weight_le_extend hbest.1).trans (hmax (extend hbest.1) hallowed)
  rw [assignmentWeight_decode] at hdominates
  have hleft := hbest.2 (decode weights assignment) (decode_valid weights assignment)
  have hright := hbest.2 (decode weights assignment.symm) (decode_valid weights assignment.symm)
  have hl : weight weights (decode weights assignment) = weight weights best := by linarith
  have hr : weight weights (decode weights assignment.symm) = weight weights best := by linarith
  constructor
  · refine ⟨decode_valid weights assignment,?_⟩
    intro other hv
    rw [hl]
    exact hbest.2 other hv
  · refine ⟨decode_valid weights assignment.symm,?_⟩
    intro other hv
    rw [hr]
    exact hbest.2 other hv

end CopiedAssignmentReduction
end SubtreeProofs.WeightedMatching

end
