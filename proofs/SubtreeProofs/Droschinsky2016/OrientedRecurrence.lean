module

public import SubtreeProofs.Droschinsky2016.RootedRecurrence
public import SubtreeProofs.Shared.RootedFork
import Mathlib.Tactic

/-!
# The matching recurrence inside fixed descendant orientations

The original whole-tree equation is extended to every pair of descendant
subproblems without changing the ambient roots during recursion. Continuation
witnesses are restricted and assembled using their actual ancestor regions.
-/

@[expose] public section

namespace SubtreeProofs.Droschinsky2016.Oriented

variable {V W K : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

noncomputable def childWeights (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (leftBase : V) (rightBase : W) (u : V) (v : W)
    (c : V) (d : W) : Option (WithBot K) := by
  classical
  exact if left.Child leftBase u c ∧ right.Child rightBase v d then
    some (weights.edge s(u,c) s(v,d) + rootedValue left right weights leftBase rightBase c d)
  else none

omit [IsStrictOrderedRing K] in
@[simp] theorem childWeights_allowed (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (leftBase : V) (rightBase : W) (u c : V) (v d : W) :
    childWeights left right weights leftBase rightBase u v c d ≠ none ↔
      left.Child leftBase u c ∧ right.Child rightBase v d := by
  classical
  simp [childWeights]

omit [IsStrictOrderedRing K] in
theorem childWeights_get (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (leftBase : V) (rightBase : W) (root child : V × W)
    (ha : left.Child leftBase root.1 child.1 ∧ right.Child rightBase root.2 child.2) :
    (childWeights left right weights leftBase rightBase root.1 root.2 child.1 child.2).getD 0 =
      weights.edge ((s(root,child)).map Prod.fst) ((s(root,child)).map Prod.snd) +
        rootedValue left right weights leftBase rightBase child.1 child.2 := by
  simp [childWeights, ha]

/-- Every selected immediate neighbor is a child in the original orientations. -/
theorem RootedValid.child_matching {left : FiniteTree V} {right : FiniteTree W}
    {leftBase u : V} {rightBase v : W} {pairs : Mapping V W}
    (h : RootedValid left right leftBase rightBase u v pairs) (weights : Scoring V W K) :
    WeightedMatching.Valid (childWeights left right weights leftBase rightBase u v)
      (childMapping left u pairs) := by
  refine ⟨?_, ?_, ?_⟩
  · intro child hc
    have hm := (mem_childMapping left u pairs child).mp hc
    exact (childWeights_allowed _ _ _ _ _ _ _ _ _).mpr
      ⟨⟨hm.2, (h.2.2 child hm.1).1⟩,
        ⟨(h.1.2.2.2.2 (u,v) h.2.1 child hm.1).mp hm.2, (h.2.2 child hm.1).2⟩⟩
  · intro p hp q hq he
    exact h.1.2.1.1 p ((mem_childMapping _ _ _ _).mp hp).1 q ((mem_childMapping _ _ _ _).mp hq).1 he
  · intro p hp q hq he
    exact h.1.2.1.2 p ((mem_childMapping _ _ _ _).mp hp).1 q ((mem_childMapping _ _ _ _).mp hq).1 he

omit [Fintype V] [Fintype W] in
/-- Restriction preserves the fixed input orientations, not just the temporary
orientation rooted at the currently mapped pair. -/
theorem RootedValid.child_branch {left : FiniteTree V} {right : FiniteTree W}
    {leftBase u : V} {rightBase v : W} {pairs : Mapping V W}
    (h : RootedValid left right leftBase rightBase u v pairs) (child : V × W)
    (hc : child ∈ childMapping left u pairs) :
    RootedValid left right leftBase rightBase child.1 child.2 (branchMapping left u child.1 pairs) := by
  have hb := h.1.child_branch_rooted (u,v) child h.2.1 hc
  refine ⟨hb.1, hb.2.1, ?_⟩
  intro p hp
  have hm := (mem_branchMapping left u child.1 pairs p).mp hp
  have hregion := h.2.2 p hm.1
  have hbranch := hb.2.2 p hp
  exact ⟨left.suffix_ancestor hregion.1 hbranch.1, right.suffix_ancestor hregion.2 hbranch.2⟩

/-- Choose independently attaining continuations for any compatible matching. -/
noncomputable def familyOfMatching (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (leftBase : V) (rightBase : W) (root : V × W)
    (children : Mapping V W)
    (hm : WeightedMatching.Valid (childWeights left right weights leftBase rightBase root.1 root.2) children) :
    BranchFamily left right root where
  children := children
  injective := hm.2
  adjacent := fun child hc =>
    let ha := (childWeights_allowed _ _ _ _ _ _ _ _ _).mp (hm.1 child hc)
    ⟨ha.1.1, ha.2.1⟩
  continuation := fun child =>
    (rootedValue_attained left right weights leftBase child.1 rightBase child.2).choose
  valid := by
    intro child hc
    have ha := (childWeights_allowed _ _ _ _ _ _ _ _ _).mp (hm.1 child hc)
    have hv := (rootedValue_attained left right weights leftBase child.1 rightBase child.2).choose_spec.1
    refine ⟨hv.1, hv.2.1, ?_⟩
    intro p hp
    exact ⟨left.ancestor_interval ha.1.2 (hv.2.2 p hp).1,
      right.ancestor_interval ha.2.2 (hv.2.2 p hp).2⟩

theorem familyOfMatching_rooted (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (leftBase : V) (rightBase : W) (root : V × W)
    (children : Mapping V W)
    (hm : WeightedMatching.Valid (childWeights left right weights leftBase rightBase root.1 root.2) children) :
    let family := familyOfMatching left right weights leftBase rightBase root children hm
    RootedValid left right leftBase rightBase root.1 root.2
      (assemble root family.children family.continuation) := by
  let family := familyOfMatching left right weights leftBase rightBase root children hm
  refine ⟨family.assemble_valid, (mem_assemble _ _ _ _).mpr (Or.inl rfl), ?_⟩
  intro p hp
  rcases (mem_assemble _ _ _ _).mp hp with rfl | ⟨child, hc, hp⟩
  · exact ⟨left.ancestor_refl _ _, right.ancestor_refl _ _⟩
  · have ha := (childWeights_allowed _ _ _ _ _ _ _ _ _).mp (hm.1 child hc)
    have hv := (rootedValue_attained left right weights leftBase child.1 rightBase child.2).choose_spec.1
    exact ⟨left.ancestor_trans ha.1.2 (hv.2.2 p hp).1, right.ancestor_trans ha.2.2 (hv.2.2 p hp).2⟩

omit [IsStrictOrderedRing K] in
theorem familyOfMatching_score (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (leftBase : V) (rightBase : W) (root : V × W)
    (children : Mapping V W)
    (hm : WeightedMatching.Valid (childWeights left right weights leftBase rightBase root.1 root.2) children) :
    let family := familyOfMatching left right weights leftBase rightBase root children hm
    score left weights (assemble root family.children family.continuation) = weights.node root.1 root.2 +
      WeightedMatching.weight (childWeights left right weights leftBase rightBase root.1 root.2) children := by
  let family := familyOfMatching left right weights leftBase rightBase root children hm
  change score left weights (assemble root family.children family.continuation) = _
  rw [family.score_assemble]
  congr 1
  apply Finset.sum_congr rfl
  intro child hc
  have hs := (rootedValue_attained left right weights leftBase child.1 rightBase child.2).choose_spec.2
  change weights.edge _ _ + score left weights
    (rootedValue_attained left right weights leftBase child.1 rightBase child.2).choose = _
  rw [hs]
  exact (childWeights_get left right weights leftBase rightBase root child
    ((childWeights_allowed _ _ _ _ _ _ _ _ _).mp (hm.1 child hc))).symm

noncomputable def bestChildMatching (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (leftBase : V) (rightBase : W) (u : V) (v : W) : Mapping V W :=
  WeightedMatching.exhaustive Finset.univ.toList (childWeights left right weights leftBase rightBase u v)

omit [IsStrictOrderedRing K] in
theorem bestChildMatching_correct (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (leftBase : V) (rightBase : W) (u : V) (v : W) :
    WeightedMatching.IsMaximum (childWeights left right weights leftBase rightBase u v)
      (bestChildMatching left right weights leftBase rightBase u v) := by
  apply WeightedMatching.exhaustive_correct
  intro p
  exact Finset.mem_toList.mpr (Finset.mem_univ p)

/-- Equation (1) holds at every fixed-orientation descendant pair. -/
theorem rooted_matching_recurrence (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (leftBase : V) (rightBase : W) (u : V) (v : W) :
    rootedValue left right weights leftBase rightBase u v = weights.node u v +
      WeightedMatching.weight (childWeights left right weights leftBase rightBase u v)
        (bestChildMatching left right weights leftBase rightBase u v) := by
  apply le_antisymm
  · obtain ⟨pairs, hv, hs⟩ := rootedValue_attained left right weights leftBase u rightBase v
    have hm := RootedValid.child_matching hv weights
    rw [← hs, hv.1.score_decomposition (u,v) hv.2.1]
    apply (add_le_add le_rfl ?_).trans
      (add_le_add le_rfl ((bestChildMatching_correct left right weights leftBase rightBase u v).2 _ hm))
    apply Finset.sum_le_sum
    intro child hc
    rw [childWeights_get left right weights leftBase rightBase (u,v) child
      ((childWeights_allowed _ _ _ _ _ _ _ _ _).mp (hm.1 child hc))]
    exact add_le_add le_rfl (rooted_score_le_value weights (RootedValid.child_branch hv child hc))
  · let children := bestChildMatching left right weights leftBase rightBase u v
    have hm := (bestChildMatching_correct left right weights leftBase rightBase u v).1
    have hv := familyOfMatching_rooted left right weights leftBase rightBase (u,v) children hm
    have hle := rooted_score_le_value weights hv
    rw [familyOfMatching_score left right weights leftBase rightBase (u,v) children hm] at hle
    exact hle

end SubtreeProofs.Droschinsky2016.Oriented

end
