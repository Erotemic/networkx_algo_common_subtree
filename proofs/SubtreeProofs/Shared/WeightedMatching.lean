module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.List.MinMax
import Mathlib.Tactic

/-!
# Finite maximum-weight partial matchings

Weights can be signed; `none` forbids a pair. Unmatched vertices and the empty
matching are permitted. The exhaustive solver enumerates subsets of the full
bipartite product, independently of Hungarian assignment or any tree DP.
-/

@[expose] public section

namespace SubtreeProofs.WeightedMatching

variable {L R : Type*} [DecidableEq L] [DecidableEq R]

/-- A compatible set of pairs with no repeated left or right endpoint. -/
def Valid (weights : L → R → Option Int) (pairs : Finset (L × R)) : Prop :=
  (∀ p ∈ pairs, weights p.1 p.2 ≠ none) ∧
  (∀ p ∈ pairs, ∀ q ∈ pairs, p.1 = q.1 → p = q) ∧
  (∀ p ∈ pairs, ∀ q ∈ pairs, p.2 = q.2 → p = q)

instance (weights : L → R → Option Int) (pairs : Finset (L × R)) :
    Decidable (Valid weights pairs) := by unfold Valid; infer_instance

/-- Each selected pair contributes exactly once. Forbidden pairs have value
zero here; feasibility is imposed independently by `Valid`. -/
def weight (weights : L → R → Option Int) (pairs : Finset (L × R)) : Int :=
  ∑ p ∈ pairs, (weights p.1 p.2).getD 0

/-- Optimality over every independently valid partial matching. -/
def IsMaximum (weights : L → R → Option Int) (pairs : Finset (L × R)) : Prop :=
  Valid weights pairs ∧ ∀ other, Valid weights other → weight weights other ≤ weight weights pairs

omit [DecidableEq L] [DecidableEq R] in
@[simp] theorem valid_empty (weights : L → R → Option Int) : Valid weights ∅ := by
  simp [Valid]

omit [DecidableEq L] [DecidableEq R] in
@[simp] theorem weight_empty (weights : L → R → Option Int) : weight weights ∅ = 0 := by
  simp [weight]


/-- Enumerate every subset of a finite list, allowing duplicate results. -/
def subsets {α : Type*} [DecidableEq α] : List α → List (Finset α)
  | [] => [∅]
  | x :: xs => subsets xs ++ (subsets xs).map (insert x)

/-- Enumeration completeness is a subset theorem, independent of matching. -/
theorem mem_subsets_iff {α : Type*} [DecidableEq α] (xs : List α) (s : Finset α) :
    s ∈ subsets xs ↔ s ⊆ xs.toFinset := by
  induction xs generalizing s with
  | nil => simp [subsets]
  | cons x xs ih =>
    simp only [subsets, List.mem_append, List.mem_map, ih]
    constructor
    · rintro (hs | ⟨t, ht, rfl⟩)
      · exact hs.trans (by simp)
      · intro a ha
        simp only [Finset.mem_insert] at ha
        rcases ha with rfl | ha
        · simp
        · simpa using Finset.mem_insert_of_mem (ht ha)
    · intro hs
      by_cases hx : x ∈ s
      · right
        refine ⟨s.erase x, ?_, Finset.insert_erase hx⟩
        intro a ha
        have hmem := hs (Finset.mem_of_mem_erase ha)
        simpa [Finset.ne_of_mem_erase ha] using hmem
      · left
        intro a ha
        have hmem := hs ha
        have hne : a ≠ x := by intro h; subst a; exact hx ha
        simpa [hne] using hmem

/-- Feasible candidates from an explicit list of all bipartite pairs. -/
def candidates (allPairs : List (L × R)) (weights : L → R → Option Int) : List (Finset (L × R)) :=
  (subsets allPairs).filter (Valid weights)

/-- Exact correspondence with the independent feasible set. -/
theorem mem_candidates (allPairs : List (L × R)) (weights : L → R → Option Int)
    (complete : ∀ p, p ∈ allPairs) (pairs : Finset (L × R)) :
    pairs ∈ candidates allPairs weights ↔ Valid weights pairs := by
  simp only [candidates, List.mem_filter, decide_eq_true_eq, mem_subsets_iff]
  have hsub : pairs ⊆ allPairs.toFinset := by
    intro p _
    exact List.mem_toFinset.mpr (complete p)
  simp [hsub]

/-- Executable exhaustive optimizer with deterministic list tie choices. -/
def exhaustive (allPairs : List (L × R)) (weights : L → R → Option Int) : Finset (L × R) :=
  ((candidates allPairs weights).argmax (weight weights)).getD ∅

/-- Global optimality of the executable exhaustive matching oracle. -/
theorem exhaustive_correct (allPairs : List (L × R)) (weights : L → R → Option Int)
    (complete : ∀ p, p ∈ allPairs) :
    IsMaximum weights (exhaustive allPairs weights) := by
  have hempty : (∅ : Finset (L × R)) ∈ candidates allPairs weights :=
    (mem_candidates allPairs weights complete ∅).mpr (valid_empty weights)
  have hnonempty : candidates allPairs weights ≠ [] := by
    intro h
    simp [h] at hempty
  have harg : (candidates allPairs weights).argmax (weight weights) ≠ none := by
    intro h
    exact hnonempty (List.argmax_eq_none.mp h)
  obtain ⟨best, hbest⟩ := Option.ne_none_iff_exists'.mp harg
  have hmem : best ∈ (candidates allPairs weights).argmax (weight weights) := by simp [hbest]
  have hout : exhaustive allPairs weights = best := by simp [exhaustive, hbest]
  rw [hout]
  constructor
  · exact (mem_candidates allPairs weights complete best).mp (List.argmax_mem hmem)
  · intro other hother
    exact List.le_of_mem_argmax ((mem_candidates allPairs weights complete other).mpr hother) hmem

/-- A rectangular finite matrix supplies its allPairs without hypotheses. -/
def solveMatrix (n m : Nat) (weights : Fin n → Fin m → Option Int) : Finset (Fin n × Fin m) :=
  exhaustive ((List.finRange n).product (List.finRange m)) weights

/-- Correctness includes empty sides, forbidden edges, and negative weights. -/
theorem solveMatrix_correct (n m : Nat) (weights : Fin n → Fin m → Option Int) :
    IsMaximum weights (solveMatrix n m weights) := by
  unfold solveMatrix
  apply exhaustive_correct
  rintro ⟨i, j⟩
  exact List.mem_product.mpr ⟨List.mem_finRange i, List.mem_finRange j⟩

omit [DecidableEq L] [DecidableEq R] in
/-- Optional unmatched endpoints ensure the optimum is nonnegative even when
all compatible edge weights are negative. -/
theorem maximum_weight_nonnegative {weights : L → R → Option Int} {pairs : Finset (L × R)}
    (h : IsMaximum weights pairs) : 0 ≤ weight weights pairs := by
  simpa using h.2 ∅ (valid_empty weights)

end SubtreeProofs.WeightedMatching

end
