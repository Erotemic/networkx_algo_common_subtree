module

public import SubtreeProofs.Shared.MatchingDeletion
public import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic

/-!
# Complete uniform matching instances

The maximum-cardinality diagonal is maximum weight when every pair has the
same nonnegative mathematical weight. This is the mathematical justification
for the production uniform-matrix fast path. It does not identify abstract
ordered-ring operations with IEEE-754 execution, or prove the Rust caller.
-/

@[expose] public section

namespace SubtreeProofs.WeightedMatching

variable {L R K : Type*} [DecidableEq L] [DecidableEq R]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

omit [DecidableEq L] [DecidableEq R] [LinearOrder K] [IsStrictOrderedRing K] in
/-- Uniform scores depend only on cardinality, independently of a solver. -/
theorem weight_uniform (value : K) (pairs : Finset (L × R)) :
    weight (fun _ _ => some value) pairs = (pairs.card : K) * value := by
  simp [weight, nsmul_eq_mul]

/-- A full matching of the smaller side attains the independent upper bound. -/
theorem uniform_isMaximum_of_card [Fintype L] [Fintype R]
    (value : K) (hvalue : 0 ≤ value) (pairs : Finset (L × R))
    (hvalid : Valid (fun _ _ => some value) pairs)
    (hcard : pairs.card = min (Fintype.card L) (Fintype.card R)) :
    IsMaximum (fun _ _ => some value) pairs := by
  refine ⟨hvalid, ?_⟩
  intro other hother
  have hbound : other.card ≤ pairs.card := by
    rw [hcard, ← matchedRight_card hother]
    exact deletion_repair_card_bound hother
  rw [weight_uniform, weight_uniform]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hbound) hvalue

/-- Original integer coordinates of the complete instance's diagonal. -/
def diagonalPair (left right : Nat) (i : Fin (min left right)) : Fin left × Fin right :=
  (⟨i.val, lt_of_lt_of_le i.isLt (min_le_left _ _)⟩,
   ⟨i.val, lt_of_lt_of_le i.isLt (min_le_right _ _)⟩)

/-- A concrete candidate, defined as a finite set rather than an algorithmic DP. -/
def diagonalPairs (left right : Nat) : Finset (Fin left × Fin right) :=
  Finset.univ.image (diagonalPair left right)

@[simp] theorem diagonalPairs_card (left right : Nat) :
    (diagonalPairs left right).card = min left right := by
  unfold diagonalPairs
  rw [Finset.card_image_iff.mpr ?_]
  · simp
  · intro i _ j _ he
    apply Fin.ext
    exact congrArg (fun p : Fin left × Fin right => p.1.val) he

omit [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] in
/-- Every original endpoint is used at most once. -/
theorem diagonalPairs_valid (left right : Nat) (value : K) :
    Valid (fun _ _ => some value) (diagonalPairs left right) := by
  refine ⟨by simp, ?_, ?_⟩
  all_goals
    intro p hp q hq he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    apply congrArg (diagonalPair left right)
    apply Fin.ext
    have hv := congrArg Fin.val he
    exact hv

/-- A complete uniform instance has a concrete optimum even for empty or
asymmetric sides. The score is the smaller cardinality times its weight. -/
theorem diagonalPairs_isMaximum (left right : Nat) (value : K) (hvalue : 0 ≤ value) :
    IsMaximum (fun _ _ => some value) (diagonalPairs left right) := by
  apply uniform_isMaximum_of_card value hvalue _ (diagonalPairs_valid left right value)
  simp

end SubtreeProofs.WeightedMatching

end
