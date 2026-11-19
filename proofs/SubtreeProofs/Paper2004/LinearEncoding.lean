module

public import SubtreeProofs.Paper2004.BalancedSequence

/-!
# Linear-time accumulator encoding (Fact 1)

This encoder uses only list constructors, never concatenation. Its cost counts
one unit for visiting a tree constructor, one for inspecting a forest cell,
and one for allocating each output step. Pair formation, projections and
fixed-size arithmetic are constant-time bookkeeping in this model.
-/

@[expose] public section

namespace SubtreeProofs.Paper2004.OrderedTree

mutual
  /-- Encode a tree before a suffix, counting constructor visits and output allocation. -/
  def encodeAccum (tree : OrderedTree) (suffix : List DyckStep) : List DyckStep × Nat :=
    match tree with
    | .node forest =>
      let result := encodeForestAccum forest suffix
      (result.1, result.2 + 1)

  /-- Encode an ordered forest by prepending each child's opening/closing steps. -/
  def encodeForestAccum (forest : List OrderedTree) (suffix : List DyckStep) : List DyckStep × Nat :=
    match forest with
    | [] => (suffix, 1)
    | tree :: rest =>
      let tailResult := encodeForestAccum rest suffix
      let headResult := encodeAccum tree (.D :: tailResult.1)
      (.U :: headResult.1, tailResult.2 + headResult.2 + 3)
end

mutual
  /-- The accumulator encoder has exactly the independently specified output. -/
  theorem encodeAccum_output (tree : OrderedTree) (suffix : List DyckStep) :
      (encodeAccum tree suffix).1 = tree.encodeDyck.toList ++ suffix := by
    cases tree with
    | node forest => exact encodeForestAccum_output forest suffix

  theorem encodeForestAccum_output (forest : List OrderedTree) (suffix : List DyckStep) :
      (encodeForestAccum forest suffix).1 = (encodeForestDyck forest).toList ++ suffix := by
    cases forest with
    | nil => rfl
    | cons tree rest =>
      simp only [encodeForestAccum, encodeAccum_output, encodeForestAccum_output]
      change DyckStep.U :: (tree.encodeDyck.toList ++ DyckStep.D ::
        ((encodeForestDyck rest).toList ++ suffix)) =
        (([DyckStep.U] ++ tree.encodeDyck.toList ++ [DyckStep.D]) ++
          (encodeForestDyck rest).toList) ++ suffix
      simp only [List.append_assoc, List.cons_append, List.nil_append]
end

mutual
  /-- Exact cost for a tree with n edges: 5*n+2 primitive operations. -/
  theorem encodeAccum_cost (tree : OrderedTree) (suffix : List DyckStep) :
      (encodeAccum tree suffix).2 = 5 * tree.edgeCount + 2 := by
    cases tree with
    | node forest =>
      simp only [encodeAccum, encodeForestAccum_cost, edgeCount_node]


  /-- The forest variant has one fewer tree-constructor visit. -/
  theorem encodeForestAccum_cost (forest : List OrderedTree) (suffix : List DyckStep) :
      (encodeForestAccum forest suffix).2 = 5 * forestEdgeCount forest + 1 := by
    cases forest with
    | nil => rfl
    | cons tree rest =>
      simp only [encodeForestAccum, encodeAccum_cost, encodeForestAccum_cost,
        forestEdgeCount_cons]
      omega
end

/-- Fact 1 with a concrete executable computation and a linear work bound. -/
theorem encodeAccum_linear (tree : OrderedTree) :
    (encodeAccum tree []).1 = tree.encodeDyck.toList ∧
      (encodeAccum tree []).2 ≤ 5 * tree.vertexCount := by
  constructor
  · simpa only [List.append_nil] using encodeAccum_output tree []
  · rw [encodeAccum_cost, vertexCount]
    omega

end SubtreeProofs.Paper2004.OrderedTree

end
