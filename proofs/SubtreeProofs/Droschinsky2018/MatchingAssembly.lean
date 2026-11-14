module

public import SubtreeProofs.Droschinsky2018.MappedAssembly
public import SubtreeProofs.Droschinsky2018.BranchOptimum
public import SubtreeProofs.Shared.WeightedMatching

/-!
# Certified matching choices assemble actual mapped-state witnesses

Every compatible partial child matching can choose attaining continuations
and construct a parent witness with exactly the matching objective. The finite
certified matching oracle therefore gives a lower bound on the independent
mapped-state optimum. The converse decomposition is proved separately.
-/

@[expose] public section

namespace SubtreeProofs.Droschinsky2018

open Droschinsky2016

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

noncomputable def stateChildWeights (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W) (penalty : WithTop ℝ) (leftBase : V) (rightBase : W)
    (u : V) (v : W) (c : V) (d : W) : Option (WithBot ℝ) := by
  classical
  exact if left.Child leftBase u c ∧ right.Child rightBase v d then
    some (matchingBranchValue left right weights penalty leftBase rightBase u v c d) else none

@[simp] theorem stateChildWeights_allowed (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W) (penalty : WithTop ℝ) (leftBase : V) (rightBase : W)
    (u : V) (v : W) (c : V) (d : W) :
    stateChildWeights left right weights penalty leftBase rightBase u v c d ≠ none ↔
      left.Child leftBase u c ∧ right.Child rightBase v d := by
  classical
  simp [stateChildWeights]

theorem stateChildWeights_get (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W) (penalty : WithTop ℝ) (leftBase : V) (rightBase : W)
    (u : V) (v : W) (c : V) (d : W) (ha : left.Child leftBase u c ∧ right.Child rightBase v d) :
    (stateChildWeights left right weights penalty leftBase rightBase u v c d).getD 0 =
      matchingBranchValue left right weights penalty leftBase rightBase u v c d := by
  simp [stateChildWeights, ha]

/-- Pick actual optimum branch witnesses for any compatible child matching. -/
noncomputable def familyOfMatching (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W) (penalty : WithTop ℝ) (leftBase : V) (rightBase : W)
    (u : V) (v : W) (children : Mapping V W)
    (hm : WeightedMatching.Valid (stateChildWeights left right weights penalty leftBase rightBase u v) children) :
    BoundaryFamily left right leftBase rightBase u v where
  children := children
  injective := hm.2
  adjacent := fun child hc => (stateChildWeights_allowed _ _ _ _ _ _ _ _ _ _).mp (hm.1 child hc)
  witness := fun child => by
    classical
    exact if ha : left.Child leftBase u child.1 ∧ right.Child rightBase v child.2 then
      (matchingBranchValue_attained weights penalty ha.1 ha.2).choose else ({child},child)
  valid := by
    classical
    intro child hc
    split
    · rename_i ha
      exact (matchingBranchValue_attained weights penalty ha.1 ha.2).choose_spec.1
    · rename_i hn
      exact False.elim (hn ((stateChildWeights_allowed _ _ _ _ _ _ _ _ _ _).mp (hm.1 child hc)))

/-- Chosen continuations attain each matrix entry with their actual path score. -/
theorem familyOfMatching_reward (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W) (penalty : WithTop ℝ) (leftBase : V) (rightBase : W)
    (u : V) (v : W) (children : Mapping V W)
    (hm : WeightedMatching.Valid (stateChildWeights left right weights penalty leftBase rightBase u v) children)
    (child : V × W) (hc : child ∈ children) :
    let family := familyOfMatching left right weights penalty leftBase rightBase u v children hm
    pathScore left right weights penalty s(u,(family.witness child).2.1) s(v,(family.witness child).2.2) +
      score left right weights penalty (family.witness child).1 =
        (stateChildWeights left right weights penalty leftBase rightBase u v child.1 child.2).getD 0 := by
  classical
  have ha := (stateChildWeights_allowed _ _ _ _ _ _ _ _ _ _).mp (hm.1 child hc)
  dsimp only [familyOfMatching]
  rw [dite_eq_left ha, stateChildWeights_get _ _ _ _ _ _ _ _ _ _ ha]
  exact (matchingBranchValue_attained weights penalty ha.1 ha.2).choose_spec.2

/-- The concrete assembled parent's score equals the complete partial-matching objective. -/
theorem familyOfMatching_score (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W) (penalty : WithTop ℝ) (leftBase : V) (rightBase : W)
    (u : V) (v : W) (children : Mapping V W)
    (hm : WeightedMatching.Valid (stateChildWeights left right weights penalty leftBase rightBase u v) children) :
    let family := familyOfMatching left right weights penalty leftBase rightBase u v children hm
    score left right weights penalty family.pairs = weights.node u v +
      WeightedMatching.weight (stateChildWeights left right weights penalty leftBase rightBase u v) children := by
  classical
  let family := familyOfMatching left right weights penalty leftBase rightBase u v children hm
  change score left right weights penalty family.pairs = _
  rw [family.score_eq]
  have hsum : (∑ i : family.Index,
      (pathScore left right weights penalty s(u,(family.witness i.val).2.1) s(v,(family.witness i.val).2.2) +
        score left right weights penalty (family.witness i.val).1)) =
      ∑ i : family.Index, (stateChildWeights left right weights penalty leftBase rightBase u v i.val.1 i.val.2).getD 0 := by
    apply Finset.sum_congr rfl
    intro i _
    exact familyOfMatching_reward left right weights penalty leftBase rightBase u v children hm i.val i.property
  rw [hsum]
  congr 1
  exact Finset.sum_coe_sort children (fun p => (stateChildWeights left right weights penalty leftBase rightBase u v p.1 p.2).getD 0)

noncomputable def bestStateMatching (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W) (penalty : WithTop ℝ) (leftBase : V) (rightBase : W) (u : V) (v : W) : Mapping V W :=
  WeightedMatching.exhaustive Finset.univ.toList (stateChildWeights left right weights penalty leftBase rightBase u v)

theorem bestStateMatching_correct (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W) (penalty : WithTop ℝ) (leftBase : V) (rightBase : W) (u : V) (v : W) :
    WeightedMatching.IsMaximum (stateChildWeights left right weights penalty leftBase rightBase u v)
      (bestStateMatching left right weights penalty leftBase rightBase u v) := by
  apply WeightedMatching.exhaustive_correct
  intro p
  exact Finset.mem_toList.mpr (Finset.mem_univ p)

/-- Optimal child-matching assembly gives a genuine mapped-state witness and
therefore cannot exceed the independently specified mapped optimum. -/
theorem matchingValue_le_mappedValue (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W) (penalty : WithTop ℝ) (leftBase : V) (rightBase : W) (u : V) (v : W) :
    weights.node u v + WeightedMatching.weight (stateChildWeights left right weights penalty leftBase rightBase u v)
      (bestStateMatching left right weights penalty leftBase rightBase u v) ≤
        mappedValue left right weights penalty leftBase rightBase u v := by
  let children := bestStateMatching left right weights penalty leftBase rightBase u v
  have hm := (bestStateMatching_correct left right weights penalty leftBase rightBase u v).1
  let family := familyOfMatching left right weights penalty leftBase rightBase u v children hm
  have hle := stateScore_le_mappedValue weights penalty family.state_valid rfl
  rw [stateScore_mapped] at hle
  have hs : score left right weights penalty family.pairs = weights.node u v +
      WeightedMatching.weight (stateChildWeights left right weights penalty leftBase rightBase u v) children :=
    familyOfMatching_score left right weights penalty leftBase rightBase u v children hm
  rw [hs] at hle
  exact hle

end SubtreeProofs.Droschinsky2018

end
