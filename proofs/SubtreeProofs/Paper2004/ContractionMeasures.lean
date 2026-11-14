module

public import SubtreeProofs.Paper2004.TreeStateBounds
import Mathlib.Tactic

/-! # True leaves, vertex depth and decomposition bounds decrease under contraction -/

@[expose] public section

namespace SubtreeProofs.Paper2004.OrderedTree

/-- Every nonempty rooted tree has an actual leaf, including the singleton. -/
theorem leafCount_pos (tree : OrderedTree) : 0 < tree.leafCount := by
  cases tree with
  | node forest =>
    cases forest with
    | nil => decide
    | cons child rest =>
      have hh := leafCount_pos child
      change 0 < child.leafCount+forestLeafCount rest
      omega
termination_by sizeOf tree

@[simp] theorem forestLeafCount_append (left right : List OrderedTree) :
    forestLeafCount (left++right) = forestLeafCount left+forestLeafCount right := by
  induction left with
  | nil => simp only [List.nil_append,forestLeafCount,Nat.zero_add]
  | cons child rest ih => simp only [List.cons_append,forestLeafCount,ih,Nat.add_assoc]

@[simp] theorem forestDepth_append (left right : List OrderedTree) :
    forestDepth (left++right) = max (forestDepth left) (forestDepth right) := by
  induction left with
  | nil => simp only [List.nil_append,forestDepth,Nat.zero_max]
  | cons child rest ih => simp only [List.cons_append,forestDepth,ih,max_assoc]

/-- The singleton root contributes a leaf when its child forest is empty. -/
theorem leafCount_node (forest : List OrderedTree) :
    leafCount (.node forest) = max 1 (forestLeafCount forest) := by
  cases forest with
  | nil => rfl
  | cons child rest =>
    change child.leafCount+forestLeafCount rest = max 1 (child.leafCount+forestLeafCount rest)
    have hh := leafCount_pos child
    omega

theorem forestLeafCount_children_le (tree : OrderedTree) : forestLeafCount tree.children ≤ tree.leafCount := by
  cases tree with
  | node forest =>
    rw [leafCount_node]
    exact le_max_right _ _

theorem forestDepth_children_le (tree : OrderedTree) : forestDepth tree.children ≤ tree.treeDepth := by
  cases tree with
  | node forest => change forestDepth forest ≤ forestDepth forest+1; omega

/-- Contexts preserve monotonicity of actual leaf counts. -/
theorem Context.leafCount_mono (context : Context) {small large : OrderedTree} (h : small.leafCount ≤ large.leafCount) :
    (context.plug small).leafCount ≤ (context.plug large).leafCount := by
  induction context with
  | hole => exact h
  | under left right inner ih =>
    simp only [Context.plug,leafCount_node,forestLeafCount_append,forestLeafCount,Nat.add_zero]
    omega

/-- Contexts preserve monotonicity of root-to-leaf vertex depth. -/
theorem Context.treeDepth_mono (context : Context) {small large : OrderedTree} (h : small.treeDepth ≤ large.treeDepth) :
    (context.plug small).treeDepth ≤ (context.plug large).treeDepth := by
  induction context with
  | hole => exact h
  | under left right inner ih =>
    simp only [Context.plug,treeDepth,forestDepth_append,forestDepth,Nat.max_zero]
    omega

/-- Contracting any single edge cannot create an additional actual leaf. -/
theorem ContractStep.leafCount_le {before after : OrderedTree} (h : ContractStep before after) : after.leafCount ≤ before.leafCount := by
  obtain ⟨context,left,right,child,rfl,rfl⟩ := h
  apply context.leafCount_mono
  have hc := forestLeafCount_children_le child
  simp only [leafCount_node,forestLeafCount_append,forestLeafCount,Nat.add_zero]
  omega

/-- Contracting any single edge cannot increase root-to-leaf vertex depth. -/
theorem ContractStep.treeDepth_le {before after : OrderedTree} (h : ContractStep before after) : after.treeDepth ≤ before.treeDepth := by
  obtain ⟨context,left,right,child,rfl,rfl⟩ := h
  apply context.treeDepth_mono
  have hc := forestDepth_children_le child
  simp only [treeDepth,forestDepth_append,forestDepth,Nat.max_zero]
  omega

theorem embeds_leafCount_le {small large : OrderedTree} (h : Embeds small large) : small.leafCount ≤ large.leafCount := by
  induction h with
  | refl => exact le_refl _
  | tail _ hs ih => exact hs.leafCount_le.trans ih

theorem embeds_treeDepth_le {small large : OrderedTree} (h : Embeds small large) : small.treeDepth ≤ large.treeDepth := by
  induction h with
  | refl => exact le_refl _
  | tail _ hs ih => exact hs.treeDepth_le.trans ih

/-- The repaired actual-leaf/depth decomposition bound, stated on independent
trees so it can bound both original inputs and any contracted output. -/
def decompositionBound (tree : OrderedTree) : Nat :=
  tree.edgeCount*(min tree.treeDepth tree.leafCount+1)+1

theorem states_card_le_decompositionBound (tree : OrderedTree) :
    (BalancedDecomposition.states tree.encodeDyck).card ≤ decompositionBound tree := decomposition_card_bound tree

/-- Every independent contracted pattern has a decomposition bound at most
that of its original input; no output-dependent complexity parameter is needed. -/
theorem embeds_decompositionBound_le {small large : OrderedTree} (h : Embeds small large) :
    decompositionBound small ≤ decompositionBound large := by
  unfold decompositionBound
  exact Nat.add_le_add_right (Nat.mul_le_mul (embeds_edgeCount_le h)
    (Nat.add_le_add_right (min_le_min (embeds_treeDepth_le h) (embeds_leafCount_le h)) 1)) 1

end SubtreeProofs.Paper2004.OrderedTree

end
