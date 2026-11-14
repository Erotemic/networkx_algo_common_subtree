module

public import SubtreeProofs.Droschinsky2018.OverallOptima
public import SubtreeProofs.Shared.RootedEvaluationOrder
public import Mathlib.Data.Finset.Lattice.Prod
import Mathlib.Tactic

/-!
# Executable mapped/skipped table evaluation

The computation takes explicit child lists and materializes each round as a
finite association table. It enumerates only child-pair subsets for matching.
The specification remains the independent common-tree witness maximum.
This initial evaluator is a reference, with repeated rounds and exhaustive
matching; it does not claim the optimized paper complexity.
-/

@[expose] public section

namespace SubtreeProofs.Droschinsky2018.RootedDP

open Droschinsky2016

variable {V W K : Type*} [DecidableEq V] [DecidableEq W]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

abbrev State (K : Type*) := WithBot K × WithBot K
abbrev Table (V W K : Type*) := List ((V × W) × State K)

/-- A missing entry has bottom in both states. -/
def read (table : Table V W K) (u : V) (v : W) : State K :=
  (table.lookup (u,v)).getD (⊥,⊥)

/-- Empty child families have maximum bottom, preserving nonempty semantics. -/
def listMax {A : Type*} (xs : List A) (f : A → WithBot K) : WithBot K :=
  (xs.map f).foldr max ⊥

/-- Allowed matching pairs are exactly the supplied immediate-child pairs. -/
def childWeights (leftChildren : V → List V) (rightChildren : W → List W)
    (weights : Scoring V W K) (previous : V → W → State K)
    (u : V) (v : W) (c : V) (d : W) : Option (WithBot K) :=
  if c ∈ leftChildren u ∧ d ∈ rightChildren v then
    some (max (weights.edge s(u,c) s(v,d) + (previous c d).1) (previous c d).2)
  else none

/-- One synchronous update of both source states at a vertex pair. -/
def step (leftChildren : V → List V) (rightChildren : W → List W)
    (weights : Scoring V W K) (oneSkip : WithBot K) (previous : V → W → State K)
    (u : V) (v : W) : State K :=
  let matrix := childWeights leftChildren rightChildren weights previous u v
  let matching := WeightedMatching.exhaustive ((leftChildren u).product (rightChildren v)) matrix
  (weights.node u v + WeightedMatching.weight matrix matching,
    oneSkip + max (listMax (leftChildren u) (fun c => max (previous c v).1 (previous c v).2))
      (listMax (rightChildren v) (fun d => max (previous u d).1 (previous u d).2)))

/-- Each round constructs an explicit finite table before the next round. -/
def evaluate (allPairs : List (V × W)) (leftChildren : V → List V) (rightChildren : W → List W)
    (weights : Scoring V W K) (oneSkip : WithBot K) : Nat → Table V W K
  | 0 => []
  | fuel + 1 =>
    let previous := evaluate allPairs leftChildren rightChildren weights oneSkip fuel
    allPairs.map (fun p => (p, step leftChildren rightChildren weights oneSkip (read previous) p.1 p.2))

/-- Computable one-vertex penalty, including the infinite-penalty case. -/
def oneSkip (penalty : WithTop K) : WithBot K :=
  match penalty with
  | none => ⊥
  | some p => ((-p : K) : WithBot K)

/-- The public table constructor chooses its fuel from the supplied input
vertex lists, rather than accepting a correctness-dependent fuel parameter. -/
def solve (leftVertices : List V) (rightVertices : List W)
    (leftChildren : V → List V) (rightChildren : W → List W)
    (weights : Scoring V W K) (penalty : WithTop K) : Table V W K :=
  evaluate (leftVertices.product rightVertices) leftChildren rightChildren weights (oneSkip penalty)
    (leftVertices.length + rightVertices.length)

/-- Rooted embeddings may choose their common root anywhere in the two input
orientations. Only internal skipped vertices incur a penalty. -/
def rootedOptimum (leftVertices : List V) (rightVertices : List W)
    (leftChildren : V → List V) (rightChildren : W → List W)
    (weights : Scoring V W K) (penalty : WithTop K) : WithBot K :=
  let table := solve leftVertices rightVertices leftChildren rightChildren weights penalty
  listMax (leftVertices.product rightVertices) (fun p => (read table p.1 p.2).1)

omit [IsStrictOrderedRing K] in
@[simp] theorem oneSkip_eq (penalty : WithTop K) : oneSkip penalty = skippedScore penalty 1 := by
  cases penalty <;> simp [oneSkip, skippedScore]

omit [CommRing K] [IsStrictOrderedRing K] in
theorem listMax_eq_sup {A : Type*} [DecidableEq A] (xs : List A) (f : A → WithBot K) :
    listMax xs f = xs.toFinset.sup f := by
  induction xs with
  | nil => simp [listMax]
  | cons a xs ih => simpa [listMax, List.toFinset_cons] using congrArg (max (f a)) ih

omit [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem read_map (allPairs : List (V × W)) (f : V × W → State K) {u : V} {v : W}
    (hp : (u,v) ∈ allPairs) : read (allPairs.map (fun p => (p,f p))) u v = f (u,v) := by
  simp [read, List.lookup_graph f hp]

variable [Fintype V] [Fintype W]

noncomputable def sourceState (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (penalty : WithTop K) (leftBase : V) (rightBase : W)
    (u : V) (v : W) : State K :=
  (mappedValue left right weights penalty leftBase rightBase u v,
    skippedValue left right weights penalty leftBase rightBase u v)

/-- The executable update is the proved source recurrence whenever its actual
child dependencies already equal their independent witness optima. -/
theorem step_correct (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (penalty : WithTop K) (leftBase : V) (rightBase : W)
    (leftChildren : V → List V) (rightChildren : W → List W)
    (hleft : ∀ u c, c ∈ leftChildren u ↔ left.Child leftBase u c)
    (hright : ∀ v d, d ∈ rightChildren v ↔ right.Child rightBase v d)
    (previous : V → W → State K) (u : V) (v : W)
    (hprevious : ∀ p, RootedEvaluationOrder.Depends left right leftBase rightBase p (u,v) →
      previous p.1 p.2 = sourceState left right weights penalty leftBase rightBase p.1 p.2) :
    step leftChildren rightChildren weights (skippedScore penalty 1) previous u v =
      sourceState left right weights penalty leftBase rightBase u v := by
  classical
  have hmatrix : childWeights leftChildren rightChildren weights previous u v =
      stateChildWeights left right weights penalty leftBase rightBase u v := by
    funext c d
    by_cases ha : left.Child leftBase u c ∧ right.Child rightBase v d
    · have hs := hprevious (c,d) (Or.inr (Or.inr ha))
      simp [childWeights, stateChildWeights, hleft, hright, ha, hs, sourceState, matchingBranchValue]
    · simp [childWeights, stateChildWeights, hleft, hright, ha]
  have hmatching : WeightedMatching.IsMaximum
      (stateChildWeights left right weights penalty leftBase rightBase u v)
      (WeightedMatching.exhaustive ((leftChildren u).product (rightChildren v))
        (stateChildWeights left right weights penalty leftBase rightBase u v)) := by
    apply WeightedMatching.exhaustive_correct_of_allowed_complete
    rintro ⟨c,d⟩ ha
    have hc := (stateChildWeights_allowed _ _ _ _ _ _ _ _ _ _).mp ha
    exact List.mem_product.mpr ⟨(hleft u c).mpr hc.1, (hright v d).mpr hc.2⟩
  have hmatchingValue := hmatching.weight_eq
    (bestStateMatching_correct left right weights penalty leftBase rightBase u v)
  have hlset : (leftChildren u).toFinset = childVertices left leftBase u := by
    ext c
    simp [hleft]
  have hrset : (rightChildren v).toFinset = childVertices right rightBase v := by
    ext d
    simp [hright]
  have hlmax : listMax (leftChildren u) (fun c => max (previous c v).1 (previous c v).2) =
      (childVertices left leftBase u).sup (fun c =>
        max (mappedValue left right weights penalty leftBase rightBase c v)
          (skippedValue left right weights penalty leftBase rightBase c v)) := by
    rw [listMax_eq_sup, hlset]
    apply Finset.sup_congr rfl
    intro c hc
    have hs := hprevious (c,v) (Or.inl ⟨(mem_childVertices _ _ _ _).mp hc, rfl⟩)
    rw [hs]
    rfl
  have hrmax : listMax (rightChildren v) (fun d => max (previous u d).1 (previous u d).2) =
      (childVertices right rightBase v).sup (fun d =>
        max (mappedValue left right weights penalty leftBase rightBase u d)
          (skippedValue left right weights penalty leftBase rightBase u d)) := by
    rw [listMax_eq_sup, hrset]
    apply Finset.sup_congr rfl
    intro d hd
    have hs := hprevious (u,d) (Or.inr (Or.inl ⟨rfl, (mem_childVertices _ _ _ _).mp hd⟩))
    rw [hs]
    rfl
  apply Prod.ext
  · change weights.node u v + WeightedMatching.weight
        (childWeights leftChildren rightChildren weights previous u v)
        (WeightedMatching.exhaustive ((leftChildren u).product (rightChildren v))
          (childWeights leftChildren rightChildren weights previous u v)) = _
    rw [hmatrix, hmatchingValue]
    exact (mapped_recurrence left right weights penalty leftBase rightBase u v).symm
  · change skippedScore penalty 1 + max _ _ = _
    rw [hlmax, hrmax]
    exact (skipped_recurrence_two_state left right weights penalty leftBase rightBase u v).symm

/-- Sufficient rounds are derived from the actual tree-depth rank; no guessed
fixed point, acyclicity certificate or optimality assumption is supplied. -/
theorem evaluate_correct (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (penalty : WithTop K) (leftBase : V) (rightBase : W)
    (allPairs : List (V × W)) (complete : ∀ p, p ∈ allPairs)
    (leftChildren : V → List V) (rightChildren : W → List W)
    (hleft : ∀ u c, c ∈ leftChildren u ↔ left.Child leftBase u c)
    (hright : ∀ v d, d ∈ rightChildren v ↔ right.Child rightBase v d)
    (fuel : Nat) (u : V) (v : W)
    (hrank : RootedEvaluationOrder.rank left right leftBase rightBase (u,v) < fuel) :
    read (evaluate allPairs leftChildren rightChildren weights (skippedScore penalty 1) fuel) u v =
      sourceState left right weights penalty leftBase rightBase u v := by
  induction fuel generalizing u v with
  | zero => omega
  | succ fuel ih =>
    rw [evaluate, read_map allPairs _ (complete (u,v))]
    apply step_correct left right weights penalty leftBase rightBase leftChildren rightChildren hleft hright
    rintro ⟨c,d⟩ hp
    apply ih
    change RootedEvaluationOrder.rank left right leftBase rightBase (c,d) < fuel
    have hd := RootedEvaluationOrder.rank_decreases left right leftBase rightBase hp
    change RootedEvaluationOrder.rank left right leftBase rightBase (c,d) <
      RootedEvaluationOrder.rank left right leftBase rightBase (u,v) at hd
    omega

/-- Every entry of the materialized table is the independent mapped/skipped
optimum. The hypotheses describe only the finite input representation. -/
theorem solve_correct (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (penalty : WithTop K) (leftBase : V) (rightBase : W)
    (leftVertices : List V) (rightVertices : List W)
    (hlvertices : ∀ u, u ∈ leftVertices) (hrvertices : ∀ v, v ∈ rightVertices)
    (leftChildren : V → List V) (rightChildren : W → List W)
    (hleft : ∀ u c, c ∈ leftChildren u ↔ left.Child leftBase u c)
    (hright : ∀ v d, d ∈ rightChildren v ↔ right.Child rightBase v d) (u : V) (v : W) :
    read (solve leftVertices rightVertices leftChildren rightChildren weights penalty) u v =
      sourceState left right weights penalty leftBase rightBase u v := by
  have hlset : leftVertices.toFinset = Finset.univ := by ext u; simp [hlvertices]
  have hrset : rightVertices.toFinset = Finset.univ := by ext v; simp [hrvertices]
  have hlcard : Fintype.card V ≤ leftVertices.length := by
    simpa only [hlset, Finset.card_univ] using leftVertices.toFinset_card_le
  have hrcard : Fintype.card W ≤ rightVertices.length := by
    simpa only [hrset, Finset.card_univ] using rightVertices.toFinset_card_le
  unfold solve
  rw [oneSkip_eq]
  apply evaluate_correct left right weights penalty leftBase rightBase _
    (fun p => List.mem_product.mpr ⟨hlvertices p.1, hrvertices p.2⟩) _ _ hleft hright
  have hrank := RootedEvaluationOrder.rank_lt_size left right leftBase rightBase (u,v)
  omega

/-- The executable rooted objective equals the independent nonempty source
optimum, including negative scores, forbidden labels and infinite penalties. -/
theorem rootedOptimum_correct (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (penalty : WithTop K) (leftBase : V) (rightBase : W)
    (leftVertices : List V) (rightVertices : List W)
    (hlvertices : ∀ u, u ∈ leftVertices) (hrvertices : ∀ v, v ∈ rightVertices)
    (leftChildren : V → List V) (rightChildren : W → List W)
    (hleft : ∀ u c, c ∈ leftChildren u ↔ left.Child leftBase u c)
    (hright : ∀ v d, d ∈ rightChildren v ↔ right.Child rightBase v d) :
    rootedOptimum leftVertices rightVertices leftChildren rightChildren weights penalty =
      rootedValue left right weights penalty leftBase rightBase := by
  have hvertices : (leftVertices.product rightVertices).toFinset = Finset.univ.product Finset.univ := by
    ext ⟨u,v⟩
    simp [hlvertices, hrvertices]
  unfold rootedOptimum
  rw [listMax_eq_sup, hvertices, Finset.product_eq_sprod]
  rw [Finset.sup_product_left (Finset.univ : Finset V) (Finset.univ : Finset W)
    (fun p => (read (solve leftVertices rightVertices leftChildren rightChildren weights penalty) p.1 p.2).1)]
  simp_rw [solve_correct left right weights penalty leftBase rightBase leftVertices rightVertices
    hlvertices hrvertices leftChildren rightChildren hleft hright]
  exact (rootedValue_eq_max_mapped left right weights penalty leftBase rightBase).symm

end SubtreeProofs.Droschinsky2018.RootedDP

end
