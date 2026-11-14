module

public import SubtreeProofs.Droschinsky2016.BranchAssembly
public import SubtreeProofs.Shared.WeightedMatching
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The rooted weighted matching recurrence

The optimum is independently specified by connected induced isomorphisms.
Decomposition gives the upper bound; assembly of independently optimal branch
witnesses gives the lower bound. The finite matching optimizer is deliberately
exhaustive, and carries no Hungarian or polynomial-time claim.
-/

@[expose] public section

namespace SubtreeProofs.Droschinsky2016

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- Edge reward plus the independent rooted continuation optimum. Non-child
pairs are forbidden, while arbitrary signed/bottom weights remain permitted. -/
noncomputable def childWeights (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (root : V × W) (c : V) (d : W) : Option (WithBot K) := by
  classical
  exact if left.graph.Adj root.1 c ∧ right.graph.Adj root.2 d then
    some (weights.edge s(root.1,c) s(root.2,d) + rootedValue left right weights root.1 root.2 c d)
  else none

omit [IsStrictOrderedRing K] in
@[simp] theorem childWeights_allowed (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (root : V × W) (c : V) (d : W) :
    childWeights left right weights root c d ≠ none ↔
      left.graph.Adj root.1 c ∧ right.graph.Adj root.2 d := by
  classical
  simp [childWeights]

omit [IsStrictOrderedRing K] in
theorem childWeights_get (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (root child : V × W)
    (ha : left.graph.Adj root.1 child.1 ∧ right.graph.Adj root.2 child.2) :
    (childWeights left right weights root child.1 child.2).getD 0 =
      weights.edge ((s(root,child)).map Prod.fst) ((s(root,child)).map Prod.snd) +
        rootedValue left right weights root.1 root.2 child.1 child.2 := by
  simp [childWeights, ha]

/-- A certified finite matching oracle for the rooted branch problem. -/
noncomputable def bestChildMatching (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (root : V × W) : Mapping V W :=
  WeightedMatching.exhaustive Finset.univ.toList (childWeights left right weights root)

omit [IsStrictOrderedRing K] in
theorem bestChildMatching_correct (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (root : V × W) :
    WeightedMatching.IsMaximum (childWeights left right weights root)
      (bestChildMatching left right weights root) := by
  apply WeightedMatching.exhaustive_correct
  intro p
  exact Finset.mem_toList.mpr (Finset.mem_univ p)

omit [IsStrictOrderedRing K] in
theorem Valid.childMatching_valid {left : FiniteTree V} {right : FiniteTree W}
    {pairs : Mapping V W} (h : Valid left right pairs) (root : V × W) (hr : root ∈ pairs)
    (weights : Scoring V W K) :
    WeightedMatching.Valid (childWeights left right weights root) (childMapping left root.1 pairs) := by
  refine ⟨?_, ?_, ?_⟩
  · intro child hc
    have hm := (mem_childMapping left root.1 pairs child).mp hc
    exact (childWeights_allowed _ _ _ _ _ _).mpr
      ⟨hm.2, (h.2.2.2.2 root hr child hm.1).mp hm.2⟩
  · intro p hp q hq he
    exact h.2.1.1 p ((mem_childMapping _ _ _ _).mp hp).1
      q ((mem_childMapping _ _ _ _).mp hq).1 he
  · intro p hp q hq he
    exact h.2.1.2 p ((mem_childMapping _ _ _ _).mp hp).1
      q ((mem_childMapping _ _ _ _).mp hq).1 he

omit [IsStrictOrderedRing K] in
/-- Independent optimal branch witnesses can all be selected at once. -/
noncomputable def optimalBranches (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (root : V × W) : BranchFamily left right root where
  children := bestChildMatching left right weights root
  injective := (bestChildMatching_correct left right weights root).1.2
  adjacent := fun child hc => (childWeights_allowed _ _ _ _ _ _).mp
    ((bestChildMatching_correct left right weights root).1.1 child hc)
  continuation := fun child =>
    (rootedValue_attained left right weights root.1 child.1 root.2 child.2).choose
  valid := fun child _ =>
    (rootedValue_attained left right weights root.1 child.1 root.2 child.2).choose_spec.1

omit [IsStrictOrderedRing K] in
theorem optimalBranches_score (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (root : V × W) :
    let family := optimalBranches left right weights root
    score left weights (assemble root family.children family.continuation) =
      weights.node root.1 root.2 + WeightedMatching.weight
        (childWeights left right weights root) (bestChildMatching left right weights root) := by
  let family := optimalBranches left right weights root
  change score left weights (assemble root family.children family.continuation) = _
  rw [family.score_assemble]
  congr 1
  apply Finset.sum_congr rfl
  intro child hc
  have hs : score left weights (family.continuation child) =
      rootedValue left right weights root.1 root.2 child.1 child.2 :=
    (rootedValue_attained left right weights root.1 child.1 root.2 child.2).choose_spec.2
  rw [hs]
  exact (childWeights_get left right weights root child (family.adjacent child hc)).symm

/-- 2016 Eq. (1), against the independently specified rooted optimum. -/
theorem rooted_matching_recurrence (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (root : V × W) :
    rootedValue left right weights root.1 root.2 root.1 root.2 =
      weights.node root.1 root.2 + WeightedMatching.weight
        (childWeights left right weights root) (bestChildMatching left right weights root) := by
  apply le_antisymm
  · obtain ⟨pairs, hv, hs⟩ := rootedValue_attained left right weights root.1 root.1 root.2 root.2
    rw [← hs, hv.1.score_decomposition root hv.2.1]
    apply (add_le_add le_rfl ?_).trans
      (add_le_add le_rfl ((bestChildMatching_correct left right weights root).2
        (childMapping left root.1 pairs) (hv.1.childMatching_valid root hv.2.1 weights)))
    apply Finset.sum_le_sum
    intro child hc
    have ha := (childWeights_allowed _ _ _ _ _ _).mp
      ((hv.1.childMatching_valid root hv.2.1 weights).1 child hc)
    rw [childWeights_get left right weights root child ha]
    exact add_le_add le_rfl (rooted_score_le_value weights
      (hv.1.child_branch_rooted root child hv.2.1 hc))
  · let family := optimalBranches left right weights root
    have hv : RootedValid left right root.1 root.2 root.1 root.2
        (assemble root family.children family.continuation) :=
      ⟨family.assemble_valid, (mem_assemble _ _ _ _).mpr (Or.inl rfl),
        fun p _ => ⟨left.root_ancestor _ _, right.root_ancestor _ _⟩⟩
    have hle := rooted_score_le_value weights hv
    rw [optimalBranches_score left right weights root] at hle
    exact hle

end SubtreeProofs.Droschinsky2016

end
