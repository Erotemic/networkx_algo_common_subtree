module

public import SubtreeProofs.Paper2004.OrderedTree
import Mathlib.Tactic

/-! # Independent ordered forests, vertex deletion and a virtual parent -/

@[expose] public section

namespace SubtreeProofs.Paper2004.OrderedTree

/-- A single edge contraction performed in an ordered forest. An edge can
be incident to the forest's implicit parent (`splice`), or inside one of the
forest's child trees (`inside`). -/
inductive ForestContractStep : List OrderedTree → List OrderedTree → Prop where
  | splice (left right : List OrderedTree) (child : OrderedTree) :
      ForestContractStep
        (left ++ [child] ++ right)
        (left ++ children child ++ right)
  | inside (left right : List OrderedTree) {before after : OrderedTree}
      (step : ContractStep before after) :
      ForestContractStep
        (left ++ [before] ++ right)
        (left ++ [after] ++ right)

namespace ForestContractStep

/-- An additional forest to the left does not invalidate a contraction. -/
theorem append_left (extra : List OrderedTree) {before after : List OrderedTree}
    (h : ForestContractStep before after) :
    ForestContractStep (extra ++ before) (extra ++ after) := by
  cases h with
  | splice left right child =>
      simpa only [List.append_assoc] using
        (ForestContractStep.splice (extra ++ left) right child)
  | inside left right step =>
      simpa only [List.append_assoc] using
        (ForestContractStep.inside (extra ++ left) right step)

/-- An additional forest to the right does not invalidate a contraction. -/
theorem append_right (extra : List OrderedTree) {before after : List OrderedTree}
    (h : ForestContractStep before after) :
    ForestContractStep (before ++ extra) (after ++ extra) := by
  cases h with
  | splice left right child =>
      simpa only [List.append_assoc] using
        (ForestContractStep.splice left (right ++ extra) child)
  | inside left right step =>
      simpa only [List.append_assoc] using
        (ForestContractStep.inside left (right ++ extra) step)

/-- A forest contraction is an ordinary contraction below the forest's
implicit parent, which becomes the root of the decoded tree. -/
theorem atRoot {before after : List OrderedTree}
    (h : ForestContractStep before after) :
    ContractStep (.node before) (.node after) := by
  cases h with
  | splice left right child =>
      exact ContractStep.atRoot left right child
  | inside left right step =>
      exact ContractStep.below left right step

/-- A contraction in a forest can also be performed inside a single child
whose child forest is that forest. -/
theorem nest {before after : List OrderedTree}
    (h : ForestContractStep before after) :
    ForestContractStep [.node before] [.node after] := by
  simpa only [List.nil_append, List.append_nil] using
    (ForestContractStep.inside [] [] h.atRoot)

end ForestContractStep

/-- Forest containment deletes a vertex by promoting its children, including
at the forest roots, or performs such a contraction inside a remaining tree. -/
def ForestEmbeds (small large : List OrderedTree) : Prop :=
  Relation.ReflTransGen ForestContractStep large small

/-- Every tree contraction induces one forest contraction of its root children. -/
theorem ContractStep.children {before after : OrderedTree} (h : ContractStep before after) :
    ForestContractStep before.children after.children := by
  obtain ⟨context,left,right,child,rfl,rfl⟩ := h
  cases context with
  | hole => exact ForestContractStep.splice left right child
  | under outerLeft outerRight inner =>
    exact ForestContractStep.inside outerLeft outerRight ⟨inner,left,right,child,rfl,rfl⟩

/-- Tree containment projects to containment of its ordered root-child forest. -/
theorem Embeds.children {small large : OrderedTree} (h : Embeds small large) :
    ForestEmbeds small.children large.children := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail hs.children

/-- Attaching a virtual parent exactly represents forest vertex deletions as
ordinary tree edge contractions. The parent itself is always retained. -/
theorem forestEmbeds_iff_parent (small large : List OrderedTree) :
    ForestEmbeds small large ↔ Embeds (.node small) (.node large) := by
  constructor
  · intro h
    induction h with
    | refl => exact embeds_refl _
    | tail _ hs ih => exact embeds_trans (embeds_of_step hs.atRoot) ih
  · intro h
    exact h.children

/-- Number of actual vertices in a forest, including all component roots. -/
def forestVertexCount (forest : List OrderedTree) : Nat := (forest.map vertexCount).sum

@[simp] theorem forestVertexCount_eq_edgeCount (forest : List OrderedTree) :
    forestVertexCount forest = forestEdgeCount forest := by
  induction forest with
  | nil => rfl
  | cons tree rest ih =>
    simpa only [forestVertexCount,List.map_cons,List.sum_cons,vertexCount,forestEdgeCount] using
      congrArg (fun count => tree.edgeCount+1+count) ih

/-- Independent maximum common ordered forest under vertex deletion. -/
def IsMaximumCommonForest (candidate first second : List OrderedTree) : Prop :=
  (ForestEmbeds candidate first ∧ ForestEmbeds candidate second) ∧
    ∀ other, ForestEmbeds other first ∧ ForestEmbeds other second →
      forestVertexCount other ≤ forestVertexCount candidate

/-- The virtual parent's edge optimum is exactly the original forest's vertex
optimum, without adding or subtracting an extra scored root. -/
theorem isMaximumCommonForest_iff_parent (candidate first second : List OrderedTree) :
    IsMaximumCommonForest candidate first second ↔
      IsMaximumCommon (.node candidate) (.node first) (.node second) := by
  constructor
  · rintro ⟨hc,hm⟩
    refine ⟨⟨(forestEmbeds_iff_parent _ _).mp hc.1,(forestEmbeds_iff_parent _ _).mp hc.2⟩,?_⟩
    intro other ho
    cases other with
    | node forest =>
      simpa only [forestVertexCount_eq_edgeCount,edgeCount] using
        hm forest ⟨(forestEmbeds_iff_parent _ _).mpr ho.1,(forestEmbeds_iff_parent _ _).mpr ho.2⟩
  · rintro ⟨hc,hm⟩
    refine ⟨⟨(forestEmbeds_iff_parent _ _).mpr hc.1,(forestEmbeds_iff_parent _ _).mpr hc.2⟩,?_⟩
    intro other ho
    simpa only [forestVertexCount_eq_edgeCount,edgeCount] using
      hm (.node other) ⟨(forestEmbeds_iff_parent _ _).mp ho.1,(forestEmbeds_iff_parent _ _).mp ho.2⟩

end SubtreeProofs.Paper2004.OrderedTree

end
