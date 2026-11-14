module

public import SubtreeProofs.Shared.RootedFork
import Mathlib.Tactic

/-!
# A well-founded evaluation order for fixed-orientation child recurrences

The rank is derived from actual canonical path depths in the finite trees.
It decreases for every one-child or two-child dependency in the rooted 2016
and 2018 equations. This is not an order theorem for the optimized unrooted
matching-reuse schedule.
-/

@[expose] public section

namespace SubtreeProofs.FiniteTree

variable {V : Type*} [Fintype V] (tree : FiniteTree V)

noncomputable def maxDepth (root : V) : Nat := Finset.univ.sup (tree.pathLength root)

theorem depth_le_maxDepth (root u : V) : tree.pathLength root u ≤ tree.maxDepth root :=
  Finset.le_sup (s := Finset.univ) (f := tree.pathLength root) (Finset.mem_univ u)

noncomputable def depthRank (root u : V) : Nat := tree.maxDepth root - tree.pathLength root u

/-- A concrete child dependency strictly decreases the derived rank. -/
theorem depthRank_child {root u c : V} (hc : tree.Child root u c) :
    tree.depthRank root c < tree.depthRank root u := by
  have hdepth := tree.child_depth hc
  have hbound := tree.depth_le_maxDepth root c
  unfold depthRank
  omega

end SubtreeProofs.FiniteTree

namespace SubtreeProofs.RootedEvaluationOrder

variable {V W : Type*} [Fintype V] [Fintype W]
  (left : FiniteTree V) (right : FiniteTree W) (leftBase : V) (rightBase : W)

noncomputable def rank (pair : V × W) : Nat :=
  left.depthRank leftBase pair.1 + right.depthRank rightBase pair.2

/-- Dependencies of the pair of mapped/skipped values: descend in one input
or in both inputs while preserving the two ambient orientations. -/
def Depends (child parent : V × W) : Prop :=
  (left.Child leftBase parent.1 child.1 ∧ child.2 = parent.2) ∨
  (child.1 = parent.1 ∧ right.Child rightBase parent.2 child.2) ∨
  (left.Child leftBase parent.1 child.1 ∧ right.Child rightBase parent.2 child.2)

theorem rank_decreases {child parent : V × W} (h : Depends left right leftBase rightBase child parent) :
    rank left right leftBase rightBase child < rank left right leftBase rightBase parent := by
  unfold Depends at h
  unfold rank
  rcases h with ⟨hl, he⟩ | ⟨he, hr⟩ | ⟨hl, hr⟩
  · have hc := left.depthRank_child hl
    rw [he]
    omega
  · have hc := right.depthRank_child hr
    rw [he]
    omega
  · have hcl := left.depthRank_child hl
    have hcr := right.depthRank_child hr
    omega

/-- All rooted recurrence dependencies terminate, without a supplied acyclicity
or evaluation-order hypothesis. -/
theorem wellFounded : WellFounded (Depends left right leftBase rightBase) :=
  (measure (rank left right leftBase rightBase)).wf.mono (fun _ _ h => rank_decreases left right leftBase rightBase h)

end SubtreeProofs.RootedEvaluationOrder

end
