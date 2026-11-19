module

public import SubtreeProofs.Rust.OrderedIsomorphismRepresentation
import Mathlib.Tactic

/-! # Actual Rust root-preserving ordered isomorphism refinement -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.OrderedIsomorphism

open Paper2004.OrderedTree OrderedSolver

/-- The actual source recursion safely returns the independent level witness
and its exact score. Both score additions fit by independent subtree bounds. -/
theorem rooted_common_isomorphism_refines (left right : BalancedWord)
    (hl : forestEdgeCount (toForest left) < 2^32) (hr : forestEdgeCount (toForest right) < 2^32) :
    ∃ result : CommonEmbedding,
      isomorphism.rooted_common_isomorphism left right = .ok (some result) ∧
      toForest result.word = OrderedIsoDP.level (toForest left) (toForest right) ∧
      result.edges.val = forestEdgeCount (toForest result.word) := by
  cases left with
  | Empty =>
    refine ⟨⟨.Empty,0#u32⟩,?_,?_,?_⟩
    · rw [isomorphism.rooted_common_isomorphism]
    · simp only [toForest,OrderedIsoDP.level]
    · rfl
  | Pair lh lt =>
    cases right with
    | Empty =>
      refine ⟨⟨.Empty,0#u32⟩,?_,?_,?_⟩
      · rw [isomorphism.rooted_common_isomorphism]
      · simp only [toForest,OrderedIsoDP.level]
      · rfl
    | Pair rh rt =>
      have hlSize := hl
      have hrSize := hr
      simp only [toForest,forestEdgeCount_cons,edgeCount_node] at hlSize hrSize
      obtain ⟨heads,hheadsRun,hheadsWord,hheadsScore⟩ := rooted_common_isomorphism_refines lh rh (by omega) (by omega)
      obtain ⟨tails,htailsRun,htailsWord,htailsScore⟩ := rooted_common_isomorphism_refines lt rt (by omega) (by omega)
      have hheadBound : heads.edges.val ≤ forestEdgeCount (toForest lh) := by
        rw [hheadsScore,hheadsWord]
        exact (OrderedIsoDP.level_sound _ _).1.edgeCount_le
      have htailBound : tails.edges.val ≤ forestEdgeCount (toForest lt) := by
        rw [htailsScore,htailsWord]
        exact (OrderedIsoDP.level_sound _ _).1.edgeCount_le
      obtain ⟨subtotal,hsum,hsubtotal⟩ := checked_add_success heads.edges tails.edges (by omega)
      obtain ⟨total,htotalRun,htotal⟩ := checked_add_success subtotal 1#u32 (by scalar_tac)
      obtain ⟨dropLeft,hdropLeftRun,hdropLeftWord,hdropLeftScore⟩ := rooted_common_isomorphism_refines lt (.Pair rh rt) (by omega) hr
      obtain ⟨dropRight,hdropRightRun,hdropRightWord,hdropRightScore⟩ := rooted_common_isomorphism_refines (.Pair lh lt) rt hl (by omega)
      let matched : CommonEmbedding := ⟨.Pair heads.word tails.word,total⟩
      have hmatchedScore : matched.edges.val = forestEdgeCount (toForest matched.word) := by
        dsimp only [matched,toForest]
        simp only [forestEdgeCount_cons,edgeCount_node]
        have hone : (1#u32).val = 1 := rfl
        omega
      have hmatchedWord : toForest matched.word =
          .node (OrderedIsoDP.level (toForest lh) (toForest rh))::OrderedIsoDP.level (toForest lt) (toForest rt) := by
        simp only [matched,toForest,hheadsWord,htailsWord]
      have hfirstScore := selectResult_edges matched dropLeft hmatchedScore hdropLeftScore
      refine ⟨selectResult (selectResult matched dropLeft) dropRight,?_,?_,
        selectResult_edges _ _ hfirstScore hdropRightScore⟩
      · rw [isomorphism.rooted_common_isomorphism]
        simp only [hheadsRun,htailsRun,bind_ok,lift,hsum,htotalRun,hdropLeftRun,hdropRightRun,choose_longer_correct]
        rfl
      · rw [selectResult_forest _ _ hfirstScore hdropRightScore,
          selectResult_forest matched dropLeft hmatchedScore hdropLeftScore,
          hmatchedWord,hdropLeftWord,hdropRightWord]
        simp only [toForest,OrderedIsoDP.level]
termination_by forestEdgeCount (toForest left) + forestEdgeCount (toForest right)
decreasing_by
  all_goals subst_vars
  all_goals simp only [toForest,forestEdgeCount_cons,edgeCount_node]
  all_goals omega

/-- End-to-end independent root-preserving tree optimum and exact score for
all represented input trees under the explicit u32 edge-count bounds. -/
theorem rooted_common_isomorphism_tree_correct (left right : BalancedWord)
    (hl : (toDyck left).semilength < 2^32) (hr : (toDyck right).semilength < 2^32) :
    ∃ result : CommonEmbedding,
      isomorphism.rooted_common_isomorphism left right = .ok (some result) ∧
      IsMaximumRootedIsomorphism (decodeDyck (toDyck result.word)) (decodeDyck (toDyck left)) (decodeDyck (toDyck right)) ∧
      result.edges.val = (decodeDyck (toDyck result.word)).edgeCount := by
  obtain ⟨result,hrun,hforest,hscore⟩ := rooted_common_isomorphism_refines left right (by simpa only [toForest_edges] using hl) (by simpa only [toForest_edges] using hr)
  refine ⟨result,hrun,?_,?_⟩
  · rw [toTree_decode,toTree_decode,toTree_decode,hforest]
    exact OrderedIsoDP.level_correct (.node (toForest left)) (.node (toForest right))
  · rw [toTree_decode]
    exact hscore

/-- Every independently specified pair of ordered rooted trees has a faithful
Rust representation, and its actual solver returns an independent optimum. -/
theorem rooted_common_isomorphism_of_trees (left right : Paper2004.OrderedTree)
    (hl : left.edgeCount < 2^32) (hr : right.edgeCount < 2^32) :
    ∃ result : CommonEmbedding,
      isomorphism.rooted_common_isomorphism (fromDyck left.encodeDyck) (fromDyck right.encodeDyck) = .ok (some result) ∧
      IsMaximumRootedIsomorphism (decodeDyck (toDyck result.word)) left right ∧
      result.edges.val = (decodeDyck (toDyck result.word)).edgeCount := by
  have h := rooted_common_isomorphism_tree_correct (fromDyck left.encodeDyck) (fromDyck right.encodeDyck)
    (by simpa only [toDyck_fromDyck,encodeDyck_semilength] using hl)
    (by simpa only [toDyck_fromDyck,encodeDyck_semilength] using hr)
  simpa only [toDyck_fromDyck,decodeDyck_encodeDyck] using h

end SubtreeProofs.Rust.OrderedIsomorphism

end
