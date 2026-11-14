module

public import SubtreeProofs.Paper2004.IsomorphismDynamicProgram
import Mathlib.Tactic

/-! # Separate numeric ordered-isomorphism recurrences and independent optima -/

@[expose] public section

namespace SubtreeProofs.Paper2004.OrderedTree.OrderedIsoDP

/-- Numeric root-preserving recurrence, computed without constructing witnesses. -/
def levelSize (left right : List OrderedTree) : Nat :=
  match left,right with
  | [],_ => 0
  | _,[] => 0
  | .node lh::lt,.node rh::rt =>
    max (max (levelSize lh rh + 1 + levelSize lt rt) (levelSize lt (.node rh::rt)))
      (levelSize (.node lh::lt) rt)
termination_by forestEdgeCount left + forestEdgeCount right
decreasing_by all_goals simp_all only [forestEdgeCount_cons,edgeCount_node]; omega

/-- Numeric arbitrary-root recurrence with the independently computed level state. -/
def anywhereSize (left right : List OrderedTree) : Nat :=
  match left,right with
  | [],_ => 0
  | _,[] => 0
  | .node lh::lt,.node rh::rt =>
    max (levelSize (.node lh::lt) (.node rh::rt))
      (max (max (anywhereSize lh (.node rh::rt)) (anywhereSize lt (.node rh::rt)))
        (max (anywhereSize (.node lh::lt) rh) (anywhereSize (.node lh::lt) rt)))
termination_by forestEdgeCount left + forestEdgeCount right
decreasing_by all_goals simp_all only [forestEdgeCount_cons,edgeCount_node]; omega

/-- The level computation's actual witness has exactly the separate numeric score. -/
theorem levelSize_eq (left right : List OrderedTree) :
    levelSize left right = forestEdgeCount (level left right) := by
  cases left with
  | nil => rw [levelSize,level] <;> simp
  | cons first lt =>
    cases right with
    | nil => rw [levelSize,level] <;> simp
    | cons second rt =>
      cases first with
      | node lh =>
        cases second with
        | node rh =>
          rw [levelSize,level]
          simp only [longer_edges,forestEdgeCount_cons,edgeCount_node,
            levelSize_eq lh rh,levelSize_eq lt rt,levelSize_eq lt (.node rh::rt),levelSize_eq (.node lh::lt) rt]
termination_by forestEdgeCount left + forestEdgeCount right
decreasing_by all_goals simp_all only [forestEdgeCount_cons,edgeCount_node]; omega

/-- The general computation's witness has exactly the separate numeric score. -/
theorem anywhereSize_eq (left right : List OrderedTree) :
    anywhereSize left right = forestEdgeCount (anywhere left right) := by
  cases left with
  | nil => rw [anywhereSize,anywhere] <;> simp
  | cons first lt =>
    cases right with
    | nil => rw [anywhereSize,anywhere] <;> simp
    | cons second rt =>
      cases first with
      | node lh =>
        cases second with
        | node rh =>
          rw [anywhereSize,anywhere]
          simp only [longer_edges,levelSize_eq,
            anywhereSize_eq lh (.node rh::rt),anywhereSize_eq lt (.node rh::rt),
            anywhereSize_eq (.node lh::lt) rh,anywhereSize_eq (.node lh::lt) rt]
termination_by forestEdgeCount left + forestEdgeCount right
decreasing_by all_goals simp_all only [forestEdgeCount_cons,edgeCount_node]; omega

/-- The numeric level recurrence attains and bounds the independent tree optimum. -/
theorem levelSize_optimum (left right : OrderedTree) :
    (∃ candidate, RootPrunes candidate left ∧ RootPrunes candidate right ∧
      candidate.edgeCount = levelSize left.children right.children) ∧
    ∀ candidate, RootPrunes candidate left → RootPrunes candidate right →
      candidate.edgeCount ≤ levelSize left.children right.children := by
  have h := level_correct left right
  rw [levelSize_eq]
  exact ⟨⟨.node (level left.children right.children),h.1.1,h.1.2,rfl⟩,h.2⟩

/-- The numeric general recurrence attains and bounds the independent tree optimum. -/
theorem anywhereSize_optimum (left right : OrderedTree) :
    (∃ candidate, IsomorphicSubtree candidate left ∧ IsomorphicSubtree candidate right ∧
      candidate.edgeCount = anywhereSize left.children right.children) ∧
    ∀ candidate, IsomorphicSubtree candidate left → IsomorphicSubtree candidate right →
      candidate.edgeCount ≤ anywhereSize left.children right.children := by
  have h := anywhere_correct left right
  rw [anywhereSize_eq]
  exact ⟨⟨.node (anywhere left.children right.children),h.1.1,h.1.2,rfl⟩,h.2⟩

end SubtreeProofs.Paper2004.OrderedTree.OrderedIsoDP

end
