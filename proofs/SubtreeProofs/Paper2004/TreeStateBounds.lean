module

public import SubtreeProofs.Paper2004.Decomposition
public import SubtreeProofs.Paper2004.ContractionCompleteness

/-!
# Decomposition bounds in independent tree parameters

The sequence leaf recurrence is connected to actual leaves in ordered trees,
and sequence depth to root-to-leaf vertex depth. The final estimate bounds
the real finite D family, with no assumed state-count inequality.
-/

@[expose] public section

namespace SubtreeProofs.Paper2004.OrderedTree

open BalancedDecomposition

mutual
  /-- Sequence depth is exactly the independent tree depth. -/
  theorem sequenceDepth_encodeDyck (tree : OrderedTree) :
      sequenceDepth tree.encodeDyck = tree.treeDepth := by
    cases tree with
    | node forest => exact sequenceDepth_encodeForestDyck forest

  theorem sequenceDepth_encodeForestDyck (forest : List OrderedTree) :
      sequenceDepth (encodeForestDyck forest) = forestDepth forest + 1 := by
    cases forest with
    | nil => simp [encodeForestDyck, forestDepth]
    | cons tree rest =>
      simp only [encodeForestDyck, sequenceDepth_nest_add,
        sequenceDepth_encodeDyck tree, sequenceDepth_encodeForestDyck rest, forestDepth]
      omega
end

/-- A nonempty forest has a nonempty balanced encoding. -/
theorem encodeForestDyck_cons_ne_zero (tree : OrderedTree) (rest : List OrderedTree) :
    encodeForestDyck (tree :: rest) ≠ 0 := by
  intro h
  have hc := congrArg DyckWord.semilength h
  simp only [encodeForestDyck_semilength, DyckWord.semilength_zero,
    forestEdgeCount_cons] at hc
  omega

mutual
  /-- The repaired balanced-word leaf measure counts actual tree leaves. -/
  theorem trueLeafMeasure_encodeDyck (tree : OrderedTree) :
      trueLeafMeasure tree.encodeDyck = tree.leafCount := by
    cases tree with
    | node forest =>
      cases forest with
      | nil => simp [encodeDyck, encodeForestDyck, leafCount]
      | cons tree rest => exact trueLeafMeasure_encodeForestDyck_cons tree rest
  termination_by sizeOf tree

  theorem trueLeafMeasure_encodeForestDyck_cons (tree : OrderedTree) (rest : List OrderedTree) :
      trueLeafMeasure (encodeForestDyck (tree :: rest)) = forestLeafCount (tree :: rest) := by
    rw [encodeForestDyck, trueLeafMeasure_nest_add, trueLeafMeasure_encodeDyck]
    cases rest with
    | nil => simp [encodeForestDyck, forestLeafCount]
    | cons next tail =>
      rw [ite_eq_right (encodeForestDyck_cons_ne_zero next tail),
        trueLeafMeasure_encodeForestDyck_cons]
      rfl
  termination_by sizeOf tree + sizeOf rest + 1
end

/-- Corrected Theorem 1: D is bounded using actual leaves and vertex depth. -/
theorem decomposition_card_bound (tree : OrderedTree) :
    (states tree.encodeDyck).card ≤
      tree.edgeCount * (min tree.treeDepth tree.leafCount + 1) + 1 := by
  simpa only [encodeDyck_semilength, sequenceDepth_encodeDyck, trueLeafMeasure_encodeDyck]
    using states_card_min_depth_leaf tree.encodeDyck

/-- The independent true-leaf estimate is stronger than needed by Theorem 1. -/
theorem decomposition_card_leaf_bound (tree : OrderedTree) :
    (states tree.encodeDyck).card ≤ tree.vertexCount * tree.leafCount := by
  simpa only [encodeDyck_semilength, trueLeafMeasure_encodeDyck, vertexCount]
    using (card_true_leaf_bounds tree.encodeDyck).1

end SubtreeProofs.Paper2004.OrderedTree

end
