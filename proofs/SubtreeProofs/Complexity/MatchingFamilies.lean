module

public import SubtreeProofs.Shared.UniformMatchingDeletion
public import SubtreeProofs.Shared.FiniteTree
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

/-!
# Stored pair cells in matching deletion families

Each materialized repair is tagged by its deleted original vertex, so equal
pairs in different repairs count separately. Unmatched deletions share the
base and have no extra pair cells. These are counts of a mathematical finite-
set representation, not asserted costs or actual Rust allocation theorems.
A source bridge must prove vector uniqueness, aliasing and capacity bounds.
-/

@[expose] public section

namespace SubtreeProofs.Complexity.MatchingFamilies

open WeightedMatching

variable {L R K : Type*} [DecidableEq L] [DecidableEq R]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- One distinct cell for each pair retained in each actually materialized
repair. Only deletions of matched right vertices need a separate witness. -/
def repairCells (base : Finset (L × R)) (repairs : R → Finset (L × R)) :
    Finset (Σ _ : R, L × R) :=
  (matchedRight base).sigma repairs

/-- Base storage plus the tagged repair pair cells. Fixed-size headers and
right-index metadata are separate from these pair-cell counts. -/
def storedPairs (base : Finset (L × R)) (repairs : R → Finset (L × R)) : Nat :=
  base.card + (repairCells base repairs).card

omit [IsStrictOrderedRing K] in
/-- Repair validity derives the smaller surviving-side bound for every
materialized result. No supplied repair optimum or cost oracle is used. -/
theorem repairCells_card_le [Fintype L] [Fintype R]
    (weights : L → R → Option K) (base : Finset (L × R)) (repairs : R → Finset (L × R))
    (hb : Valid weights base)
    (hr : ∀ r ∈ matchedRight base, Valid (deleteRight weights r) (repairs r)) :
    (repairCells base repairs).card ≤ base.card * min (Fintype.card L) (Fintype.card R - 1) := by
  unfold repairCells
  rw [Finset.card_sigma]
  calc
    _ ≤ ∑ _r ∈ matchedRight base, min (Fintype.card L) (Fintype.card R - 1) :=
      Finset.sum_le_sum (fun r h => deleted_matching_card_le weights r (repairs r) (hr r h))
    _ = _ := by simp [matchedRight_card hb]

omit [IsStrictOrderedRing K] in
/-- The retained pairs of a family use at most k+k² cells, where k is the
smaller original side. Sharing unused deletions is essential to this count. -/
theorem storedPairs_le [Fintype L] [Fintype R]
    (weights : L → R → Option K) (base : Finset (L × R)) (repairs : R → Finset (L × R))
    (hb : Valid weights base)
    (hr : ∀ r ∈ matchedRight base, Valid (deleteRight weights r) (repairs r)) :
    storedPairs base repairs ≤ min (Fintype.card L) (Fintype.card R) +
      min (Fintype.card L) (Fintype.card R) ^ 2 := by
  have hc := repairCells_card_le weights base repairs hb hr
  have hk := deletion_repair_card_bound hb
  rw [matchedRight_card hb] at hk
  have hs : min (Fintype.card L) (Fintype.card R - 1) ≤ min (Fintype.card L) (Fintype.card R) :=
    min_le_min le_rfl (Nat.sub_le _ _)
  unfold storedPairs
  have hm := Nat.mul_le_mul hk hs
  nlinarith

omit [IsStrictOrderedRing K] in
/-- A rectangular bound useful when aggregating many degree-indexed families. -/
theorem storedPairs_le_product [Fintype L] [Fintype R]
    (weights : L → R → Option K) (base : Finset (L × R)) (repairs : R → Finset (L × R))
    (hb : Valid weights base)
    (hr : ∀ r ∈ matchedRight base, Valid (deleteRight weights r) (repairs r)) :
    storedPairs base repairs ≤ 2 * Fintype.card L * Fintype.card R := by
  have h := storedPairs_le weights base repairs hb hr
  let k := min (Fintype.card L) (Fintype.card R)
  have hsq : k * k ≤ Fintype.card L * Fintype.card R :=
    Nat.mul_le_mul (min_le_left _ _) (min_le_right _ _)
  have hk : k ≤ k * k := by
    by_cases hz : k = 0
    · simp [hz]
    · have hp : 1 ≤ k := by omega
      nlinarith
  dsimp [k] at *
  nlinarith

/-- The concrete uniform construction satisfies the bound for all dimensions
and every right deletion, with no feasibility or cardinality premise. -/
theorem uniform_storedPairs_le (left right : Nat) :
    storedPairs (diagonalPairs left right) (uniformRightDeletion left right) ≤ 2 * left * right := by
  simpa only [Fintype.card_fin] using
    storedPairs_le_product (fun _ _ => some (1 : Int)) (diagonalPairs left right)
      (uniformRightDeletion left right) (diagonalPairs_valid left right (1 : Int))
      (fun r _ => (uniformRightDeletion_isMaximum left right r (1 : Int) (by decide)).1)

omit [IsStrictOrderedRing K] in
/-- Aggregation for arbitrary feasible weighted families. The hypotheses are
matching feasibility certificates, not assumed runtimes or optimum values. -/
theorem family_sum_le {U V : Type*} [Fintype U] [Fintype V]
    (left : U → Nat) (right : V → Nat)
    (weights : ∀ u v, Fin (left u) → Fin (right v) → Option K)
    (base : ∀ u v, Finset (Fin (left u) × Fin (right v)))
    (repairs : ∀ u v, Fin (right v) → Finset (Fin (left u) × Fin (right v)))
    (hb : ∀ u v, Valid (weights u v) (base u v))
    (hr : ∀ u v r, r ∈ matchedRight (base u v) →
      Valid (deleteRight (weights u v) r) (repairs u v r)) :
    (∑ u, ∑ v, storedPairs (base u v) (repairs u v)) ≤ 2 * (∑ u, left u) * (∑ v, right v) := by
  calc
    _ ≤ ∑ u, ∑ v, 2 * left u * right v := by
      apply Finset.sum_le_sum
      intro u _
      apply Finset.sum_le_sum
      intro v _
      simpa only [Fintype.card_fin] using
        storedPairs_le_product (weights u v) (base u v) (repairs u v) (hb u v) (hr u v)
    _ = _ := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      rw [← Finset.mul_sum]

/-- Summing concrete family storage factors into the two actual degree sums. -/
theorem uniform_family_sum_le {U V : Type*} [Fintype U] [Fintype V]
    (left : U → Nat) (right : V → Nat) :
    (∑ u, ∑ v, storedPairs (diagonalPairs (left u) (right v))
      (uniformRightDeletion (left u) (right v))) ≤ 2 * (∑ u, left u) * (∑ v, right v) := by
  exact family_sum_le left right (fun _ _ _ _ => some (1 : Int))
    (fun u v => diagonalPairs (left u) (right v))
    (fun u v => uniformRightDeletion (left u) (right v))
    (fun u v => diagonalPairs_valid (left u) (right v) (1 : Int))
    (fun u v r _ => (uniformRightDeletion_isMaximum (left u) (right v) r (1 : Int) (by decide)).1)

/-- Mathlib's handshaking and tree edge-count theorems supply the budget;
it is not assumed as a scheduler/cost hypothesis. -/
theorem tree_degree_sum {V : Type*} [Fintype V] (tree : FiniteTree V) [DecidableRel tree.graph.Adj] :
    (∑ v, tree.graph.degree v) = 2 * (Fintype.card V - 1) := by
  classical
  have he := tree.isTree.card_edgeFinset
  have hd := tree.graph.sum_degrees_eq_twice_card_edges
  omega

omit [IsStrictOrderedRing K] in
/-- Any feasible degree-indexed family collection has a quadratic pair-storage
bound. Vector refinement and the actual DP scheduling/caches are still needed
for a production space theorem. -/
theorem tree_family_pairs_le {U V : Type*} [Fintype U] [Fintype V]
    (left : FiniteTree U) (right : FiniteTree V)
    [DecidableRel left.graph.Adj] [DecidableRel right.graph.Adj]
    (weights : ∀ u v, Fin (left.graph.degree u) → Fin (right.graph.degree v) → Option K)
    (base : ∀ u v, Finset (Fin (left.graph.degree u) × Fin (right.graph.degree v)))
    (repairs : ∀ u v, Fin (right.graph.degree v) → Finset (Fin (left.graph.degree u) × Fin (right.graph.degree v)))
    (hb : ∀ u v, Valid (weights u v) (base u v))
    (hr : ∀ u v r, r ∈ matchedRight (base u v) →
      Valid (deleteRight (weights u v) r) (repairs u v r)) :
    (∑ u, ∑ v, storedPairs (base u v) (repairs u v)) ≤
      8 * (Fintype.card U - 1) * (Fintype.card V - 1) := by
  have h := family_sum_le (fun u => left.graph.degree u) (fun v => right.graph.degree v)
    weights base repairs hb hr
  rw [tree_degree_sum left, tree_degree_sum right] at h
  nlinarith

/-- Degree-indexed uniform families retain O(n*m) pair cells. This alone is
not a space theorem for the production DP, whose vectors/caches/arena still
need a representation and allocation refinement. -/
theorem uniform_tree_family_pairs_le {U V : Type*} [Fintype U] [Fintype V]
    (left : FiniteTree U) (right : FiniteTree V)
    [DecidableRel left.graph.Adj] [DecidableRel right.graph.Adj] :
    (∑ u, ∑ v, storedPairs (diagonalPairs (left.graph.degree u) (right.graph.degree v))
      (uniformRightDeletion (left.graph.degree u) (right.graph.degree v))) ≤
        8 * (Fintype.card U - 1) * (Fintype.card V - 1) := by
  have h := uniform_family_sum_le (fun u => left.graph.degree u) (fun v => right.graph.degree v)
  rw [tree_degree_sum left, tree_degree_sum right] at h
  nlinarith

end SubtreeProofs.Complexity.MatchingFamilies

end
