module

public import SubtreeProofs.Paper2004.ContractionCompleteness
public import Mathlib.Data.List.MinMax
import Mathlib.Tactic

/-!
# Exhaustive ordered-tree contraction oracle

This deliberately slow enumeration works on trees and ordered child lists.
It does not use a balanced-word recurrence. Its membership theorem identifies
its results with the independent operational contraction relation.
-/

@[expose] public section

namespace SubtreeProofs.Paper2004.OrderedTree

mutual
  /-- All trees obtained by one edge contraction. -/
  def contractOnce : OrderedTree → List OrderedTree
    | .node forest => (contractForestOnce forest).map OrderedTree.node

  /-- Contract an edge from the implicit parent or inside a forest member. -/
  def contractForestOnce : List OrderedTree → List (List OrderedTree)
    | [] => []
    | tree :: rest =>
        [tree.children ++ rest] ++
        (contractOnce tree).map (fun smaller => smaller :: rest) ++
        (contractForestOnce rest).map (fun smaller => tree :: smaller)
end

mutual
  theorem contractOnce_sound {before after : OrderedTree}
      (h : after ∈ contractOnce before) : ContractStep before after := by
    cases before with
    | node forest =>
      obtain ⟨smaller, hm, rfl⟩ := List.mem_map.mp h
      exact (contractForestOnce_sound hm).atRoot
  termination_by sizeOf before

  theorem contractForestOnce_sound {before after : List OrderedTree}
      (h : after ∈ contractForestOnce before) : ForestContractStep before after := by
    cases before with
    | nil => simp [contractForestOnce] at h
    | cons tree rest =>
      simp only [contractForestOnce, List.mem_append, List.mem_singleton,
        List.mem_map] at h
      rcases h with (rfl | ⟨smaller, hm, rfl⟩) | ⟨smaller, hm, rfl⟩
      · simpa using ForestContractStep.splice [] rest tree
      · simpa using ForestContractStep.inside [] rest (contractOnce_sound hm)
      · simpa using (contractForestOnce_sound hm).append_left [tree]
  termination_by sizeOf before
end

/-- Every splice at a specified sibling position is enumerated. -/
theorem splice_mem_contractForestOnce (left right : List OrderedTree) (child : OrderedTree) :
    left ++ children child ++ right ∈ contractForestOnce (left ++ [child] ++ right) := by
  induction left with
  | nil => simp [contractForestOnce]
  | cons tree rest ih =>
    simp only [List.cons_append]
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨_, ih, rfl⟩

/-- Every contraction inside a specified child is enumerated. -/
theorem inside_mem_contractForestOnce (left right : List OrderedTree)
    {before after : OrderedTree} (h : after ∈ contractOnce before) :
    left ++ [after] ++ right ∈ contractForestOnce (left ++ [before] ++ right) := by
  induction left with
  | nil =>
    simp only [List.nil_append, List.singleton_append, contractForestOnce]
    apply List.mem_append_left
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨_, h, rfl⟩
  | cons tree rest ih =>
    simp only [List.cons_append]
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨_, ih, rfl⟩

/-- A fixed context preserves enumeration of a contraction. -/
theorem context_mem_contractOnce (ctx : Context) {before after : OrderedTree}
    (h : after ∈ contractOnce before) :
    ctx.plug after ∈ contractOnce (ctx.plug before) := by
  induction ctx with
  | hole => exact h
  | under left right inner ih =>
    exact List.mem_map.mpr ⟨_, inside_mem_contractForestOnce left right ih, rfl⟩

/-- Every operational edge contraction appears in the enumerator. -/
theorem contractOnce_complete {before after : OrderedTree}
    (h : ContractStep before after) : after ∈ contractOnce before := by
  obtain ⟨ctx, left, right, child, rfl, rfl⟩ := h
  apply context_mem_contractOnce
  exact List.mem_map.mpr ⟨_, splice_mem_contractForestOnce left right child, rfl⟩

/-- Exact one-step enumeration, with no Dyck-word assumption. -/
theorem mem_contractOnce_iff {before after : OrderedTree} :
    after ∈ contractOnce before ↔ ContractStep before after :=
  ⟨contractOnce_sound, contractOnce_complete⟩

/-- Enumerate all contractions using at most `fuel` steps; retain the input. -/
def contractions : Nat → OrderedTree → List OrderedTree
  | 0, tree => [tree]
  | fuel + 1, tree => tree :: (contractOnce tree).flatMap (contractions fuel)

/-- Every enumerated result is an operational embedding. -/
theorem contractions_sound {fuel : Nat} {small large : OrderedTree}
    (h : small ∈ contractions fuel large) : Embeds small large := by
  induction fuel generalizing small large with
  | zero =>
    simp only [contractions, List.mem_singleton] at h
    subst small
    exact embeds_refl _
  | succ fuel ih =>
    simp only [contractions, List.mem_cons, List.mem_flatMap] at h
    rcases h with rfl | ⟨middle, hm, hs⟩
    · exact embeds_refl _
    · exact embeds_trans (ih hs) (embeds_of_step (contractOnce_sound hm))

/-- The edge difference bounds the number of steps in every contraction chain. -/
theorem contractions_complete {small large : OrderedTree} (h : Embeds small large)
    {fuel : Nat} (hfuel : edgeCount large ≤ fuel + edgeCount small) :
    small ∈ contractions fuel large := by
  induction fuel generalizing large with
  | zero =>
    rcases Relation.ReflTransGen.cases_head h with heq | ⟨middle, hs, hm⟩
    · subst large
      simp [contractions]
    · have hdrop := hs.edgeCount_decreases
      have hmid := embeds_edgeCount_le hm
      omega
  | succ fuel ih =>
    rcases Relation.ReflTransGen.cases_head h with heq | ⟨middle, hs, hm⟩
    · subst large
      exact List.mem_cons_self
    · apply List.mem_cons_of_mem
      apply List.mem_flatMap.mpr
      refine ⟨middle, contractOnce_complete hs, ih hm ?_⟩
      have hdrop := hs.edgeCount_decreases
      omega

/-- An edge-count-sized fuel budget enumerates exactly all embedded trees. -/
theorem mem_contractions_iff {small large : OrderedTree} :
    small ∈ contractions large.edgeCount large ↔ Embeds small large := by
  constructor
  · exact contractions_sound
  · intro h
    exact contractions_complete h (by omega)

/-- The singleton is obtained by contracting every edge. -/
theorem singleton_embeds (tree : OrderedTree) : Embeds singleton tree := by
  match tree with
  | .node [] => exact embeds_refl _
  | .node (child :: rest) =>
    have step : ContractStep (.node (child :: rest)) (.node (child.children ++ rest)) := by
      simpa using ContractStep.atRoot [] rest child
    exact embeds_trans (singleton_embeds (.node (child.children ++ rest))) (embeds_of_step step)
termination_by tree.edgeCount
decreasing_by
  have step := ContractStep.atRoot [] rest child
  have decrease := step.edgeCount_decreases
  simpa using show edgeCount (.node (child.children ++ rest)) <
    edgeCount (.node (child :: rest)) by simpa using (by omega :
      edgeCount (.node ([] ++ children child ++ rest)) <
      edgeCount (.node ([] ++ [child] ++ rest)))

/-- Tree equality is decidable by the already proved injective Dyck encoding. -/
instance : DecidableEq OrderedTree := fun first second =>
  decidable_of_iff (encodeDyck first = encodeDyck second)
    ⟨fun h => by simpa using congrArg decodeDyck h, congrArg encodeDyck⟩

/-- Enumerate common candidates using two independent contraction lists. -/
def commonContractions (left right : OrderedTree) : List OrderedTree :=
  (contractions left.edgeCount left).filter
    (fun tree => tree ∈ contractions right.edgeCount right)

/-- Common-candidate enumeration is exactly the independent tree specification. -/
theorem mem_commonContractions_iff {tree left right : OrderedTree} :
    tree ∈ commonContractions left right ↔ CommonEmbedding tree left right := by
  simp only [commonContractions, List.mem_filter, decide_eq_true_eq,
    mem_contractions_iff, CommonEmbedding]

/-- The exhaustive oracle returns an explicit maximum-size candidate. -/
def maximumCommonContraction (left right : OrderedTree) : OrderedTree :=
  ((commonContractions left right).argmax edgeCount).getD singleton

/-- Every input pair has a common candidate, even when both have no edges. -/
theorem singleton_mem_commonContractions (left right : OrderedTree) :
    singleton ∈ commonContractions left right :=
  mem_commonContractions_iff.mpr ⟨singleton_embeds left, singleton_embeds right⟩

/-- Full correctness of the exhaustive tree oracle against `IsMaximumCommon`.
This establishes an independent executable baseline, with no polynomial-time claim. -/
theorem maximumCommonContraction_correct (left right : OrderedTree) :
    IsMaximumCommon (maximumCommonContraction left right) left right := by
  have hnonempty : commonContractions left right ≠ [] := by
    intro heq
    have h := singleton_mem_commonContractions left right
    simp [heq] at h
  have harg : (commonContractions left right).argmax edgeCount ≠ none := by
    intro hnone
    exact hnonempty (List.argmax_eq_none.mp hnone)
  obtain ⟨best, hbest⟩ := Option.ne_none_iff_exists'.mp harg
  have hmem : best ∈ (commonContractions left right).argmax edgeCount := by
    simp [hbest]
  have hout : maximumCommonContraction left right = best := by
    simp [maximumCommonContraction, hbest]
  rw [hout]
  constructor
  · exact mem_commonContractions_iff.mp (List.argmax_mem hmem)
  · intro other hother
    exact List.le_of_mem_argmax (mem_commonContractions_iff.mpr hother) hmem

end SubtreeProofs.Paper2004.OrderedTree

end
