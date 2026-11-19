module

public import SubtreeProofs.Droschinsky2016.OrientedRecurrence
public import SubtreeProofs.Shared.FiniteTable
public import SubtreeProofs.Shared.RootedEvaluationOrder
import Mathlib.Tactic

/-!
# Executable 2016 descendant tables and unrooted rerooting baseline

Finite vertex and child lists drive a materialized table. Matching enumerates
only child pairs. The independent connected-isomorphism witness family, rather
than the recurrence, specifies every returned optimum. The unrooted entry
fixes one left orientation and tries all right roots, as in Lemma 2.
-/

@[expose] public section

namespace SubtreeProofs.Droschinsky2016.RootedDP

variable {V W K : Type*} [DecidableEq V] [DecidableEq W]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

abbrev Table (V W K : Type*) := FiniteTable.Table (V × W) (WithBot K)

def read (table : Table V W K) (u : V) (v : W) : WithBot K := FiniteTable.read ⊥ table (u,v)

def childWeights (leftChildren : V → List V) (rightChildren : W → List W)
    (weights : Scoring V W K) (previous : V → W → WithBot K)
    (u : V) (v : W) (c : V) (d : W) : Option (WithBot K) :=
  if c ∈ leftChildren u ∧ d ∈ rightChildren v then
    some (weights.edge s(u,c) s(v,d) + previous c d) else none

def step (leftChildren : V → List V) (rightChildren : W → List W)
    (weights : Scoring V W K) (previous : V → W → WithBot K) (u : V) (v : W) : WithBot K :=
  let matrix := childWeights leftChildren rightChildren weights previous u v
  weights.node u v + WeightedMatching.weight matrix
    (WeightedMatching.exhaustive ((leftChildren u).product (rightChildren v)) matrix)

def solve (leftVertices : List V) (rightVertices : List W)
    (leftChildren : V → List V) (rightChildren : W → List W) (weights : Scoring V W K) : Table V W K :=
  FiniteTable.rounds (leftVertices.product rightVertices) ⊥
    (fun previous p => step leftChildren rightChildren weights (fun u v => previous (u,v)) p.1 p.2)
    (leftVertices.length + rightVertices.length)

/-- The straightforward unrooted algorithm fixes the left orientation and
constructs one descendant table for each possible right root. -/
def unrootedOptimum (leftVertices : List V) (rightVertices : List W)
    (leftChildren : V → List V) (rightChildren : W → W → List W) (weights : Scoring V W K) : WithBot K :=
  FiniteTable.maximum rightVertices (fun root =>
    let table := solve leftVertices rightVertices leftChildren (rightChildren root) weights
    FiniteTable.maximum leftVertices (fun u => read table u root))

variable [Fintype V] [Fintype W]

theorem step_correct (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (leftBase : V) (rightBase : W)
    (leftChildren : V → List V) (rightChildren : W → List W)
    (hleft : ∀ u c, c ∈ leftChildren u ↔ left.Child leftBase u c)
    (hright : ∀ v d, d ∈ rightChildren v ↔ right.Child rightBase v d)
    (previous : V → W → WithBot K) (u : V) (v : W)
    (hprevious : ∀ p, RootedEvaluationOrder.Depends left right leftBase rightBase p (u,v) →
      previous p.1 p.2 = rootedValue left right weights leftBase rightBase p.1 p.2) :
    step leftChildren rightChildren weights previous u v = rootedValue left right weights leftBase rightBase u v := by
  classical
  have hmatrix : childWeights leftChildren rightChildren weights previous u v =
      Oriented.childWeights left right weights leftBase rightBase u v := by
    funext c d
    by_cases ha : left.Child leftBase u c ∧ right.Child rightBase v d
    · have hs := hprevious (c,d) (Or.inr (Or.inr ha))
      simp [childWeights, Oriented.childWeights, hleft, hright, ha, hs]
    · simp [childWeights, Oriented.childWeights, hleft, hright, ha]
  have hm : WeightedMatching.IsMaximum (Oriented.childWeights left right weights leftBase rightBase u v)
      (WeightedMatching.exhaustive ((leftChildren u).product (rightChildren v))
        (Oriented.childWeights left right weights leftBase rightBase u v)) := by
    apply WeightedMatching.exhaustive_correct_of_allowed_complete
    rintro ⟨c,d⟩ ha
    have hc := (Oriented.childWeights_allowed _ _ _ _ _ _ _ _ _).mp ha
    exact List.mem_product.mpr ⟨(hleft u c).mpr hc.1, (hright v d).mpr hc.2⟩
  change weights.node u v + WeightedMatching.weight
    (childWeights leftChildren rightChildren weights previous u v)
    (WeightedMatching.exhaustive ((leftChildren u).product (rightChildren v))
      (childWeights leftChildren rightChildren weights previous u v)) = _
  rw [hmatrix, hm.weight_eq (Oriented.bestChildMatching_correct left right weights leftBase rightBase u v)]
  exact (Oriented.rooted_matching_recurrence left right weights leftBase rightBase u v).symm

/-- Every table entry equals the independently specified optimum of its
actual descendant subtrees. Only representation hypotheses are supplied. -/
theorem solve_correct (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (leftBase : V) (rightBase : W)
    (leftVertices : List V) (rightVertices : List W)
    (hlvertices : ∀ u, u ∈ leftVertices) (hrvertices : ∀ v, v ∈ rightVertices)
    (leftChildren : V → List V) (rightChildren : W → List W)
    (hleft : ∀ u c, c ∈ leftChildren u ↔ left.Child leftBase u c)
    (hright : ∀ v d, d ∈ rightChildren v ↔ right.Child rightBase v d) (u : V) (v : W) :
    read (solve leftVertices rightVertices leftChildren rightChildren weights) u v =
      rootedValue left right weights leftBase rightBase u v := by
  have hlset : leftVertices.toFinset = Finset.univ := by ext u; simp [hlvertices]
  have hrset : rightVertices.toFinset = Finset.univ := by ext v; simp [hrvertices]
  have hlcard : Fintype.card V ≤ leftVertices.length := by
    simpa only [hlset, Finset.card_univ] using leftVertices.toFinset_card_le
  have hrcard : Fintype.card W ≤ rightVertices.length := by
    simpa only [hrset, Finset.card_univ] using rightVertices.toFinset_card_le
  have hrank : RootedEvaluationOrder.rank left right leftBase rightBase (u,v) <
      leftVertices.length + rightVertices.length :=
    (RootedEvaluationOrder.rank_lt_size left right leftBase rightBase (u,v)).trans_le (Nat.add_le_add hlcard hrcard)
  apply FiniteTable.rounds_correct _ ⊥ _
    (fun p => List.mem_product.mpr ⟨hlvertices p.1, hrvertices p.2⟩)
    (RootedEvaluationOrder.Depends left right leftBase rightBase)
    (RootedEvaluationOrder.rank left right leftBase rightBase)
    (fun _ _ h => RootedEvaluationOrder.rank_decreases left right leftBase rightBase h)
    (fun p => rootedValue left right weights leftBase rightBase p.1 p.2) _ _ (u,v) hrank
  intro previous p hp
  exact step_correct left right weights leftBase rightBase leftChildren rightChildren hleft hright
    (fun u v => previous (u,v)) p.1 p.2 hp

/-- Lemma 2 turns the executable rerooting baseline into an exact nonempty
unrooted optimum; no efficient matching or optimized cost claim is made. -/
theorem unrootedOptimum_correct (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (leftBase : V)
    (leftVertices : List V) (rightVertices : List W)
    (hlvertices : ∀ u, u ∈ leftVertices) (hrvertices : ∀ v, v ∈ rightVertices)
    (leftChildren : V → List V) (rightChildren : W → W → List W)
    (hleft : ∀ u c, c ∈ leftChildren u ↔ left.Child leftBase u c)
    (hright : ∀ root v d, d ∈ rightChildren root v ↔ right.Child root v d) :
    unrootedOptimum leftVertices rightVertices leftChildren rightChildren weights = unrootedValue left right weights := by
  have hlset : leftVertices.toFinset = Finset.univ := by ext u; simp [hlvertices]
  have hrset : rightVertices.toFinset = Finset.univ := by ext v; simp [hrvertices]
  unfold unrootedOptimum
  rw [FiniteTable.maximum_eq_sup, hrset]
  simp_rw [FiniteTable.maximum_eq_sup, hlset]
  have hs : ∀ root u, read (solve leftVertices rightVertices leftChildren (rightChildren root) weights) u root =
      rootedValue left right weights leftBase root u root :=
    fun root u => solve_correct left right weights leftBase root leftVertices rightVertices hlvertices hrvertices
      leftChildren (rightChildren root) hleft (hright root) u root
  simp_rw [hs]
  rw [Finset.sup_comm]
  exact fixedRootValue_eq_unrootedValue left right weights leftBase

end SubtreeProofs.Droschinsky2016.RootedDP

end
