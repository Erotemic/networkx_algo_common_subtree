module

public import SubtreeProofs.Rust.OrderedRootedIsomorphism
import Mathlib.Tactic

/-! # Actual Rust arbitrary-root ordered subtree isomorphism refinement -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.OrderedIsomorphism

open Paper2004.OrderedTree OrderedSolver

/-- The actual arbitrary-root source recursion safely returns the independent
maximum witness and its exact edge count, with source tie choices preserved. -/
theorem largest_common_isomorphism_refines (left right : BalancedWord)
    (hl : forestEdgeCount (toForest left) < 2^32) (hr : forestEdgeCount (toForest right) < 2^32) :
    ∃ result : CommonEmbedding,
      isomorphism.largest_common_isomorphism left right = .ok (some result) ∧
      toForest result.word = OrderedIsoDP.anywhere (toForest left) (toForest right) ∧
      result.edges.val = forestEdgeCount (toForest result.word) := by
  cases left with
  | Empty =>
    refine ⟨⟨.Empty,0#u32⟩,?_,?_,?_⟩
    · rw [isomorphism.largest_common_isomorphism]
    · simp only [toForest,OrderedIsoDP.anywhere]
    · rfl
  | Pair lh lt =>
    cases right with
    | Empty =>
      refine ⟨⟨.Empty,0#u32⟩,?_,?_,?_⟩
      · rw [isomorphism.largest_common_isomorphism]
      · simp only [toForest,OrderedIsoDP.anywhere]
      · rfl
    | Pair rh rt =>
      have hlSize := hl
      have hrSize := hr
      simp only [toForest,forestEdgeCount_cons,edgeCount_node] at hlSize hrSize
      obtain ⟨rooted,hrootedRun,hrootedWord,hrootedScore⟩ := rooted_common_isomorphism_refines (.Pair lh lt) (.Pair rh rt) hl hr
      obtain ⟨leftHead,hleftHeadRun,hleftHeadWord,hleftHeadScore⟩ := largest_common_isomorphism_refines lh (.Pair rh rt) (by omega) hr
      obtain ⟨leftTail,hleftTailRun,hleftTailWord,hleftTailScore⟩ := largest_common_isomorphism_refines lt (.Pair rh rt) (by omega) hr
      obtain ⟨rightHead,hrightHeadRun,hrightHeadWord,hrightHeadScore⟩ := largest_common_isomorphism_refines (.Pair lh lt) rh hl (by omega)
      obtain ⟨rightTail,hrightTailRun,hrightTailWord,hrightTailScore⟩ := largest_common_isomorphism_refines (.Pair lh lt) rt hl (by omega)
      let leftChoice := selectResult leftHead leftTail
      let rightChoice := selectResult rightHead rightTail
      let descended := selectResult leftChoice rightChoice
      have hleftScore : leftChoice.edges.val = forestEdgeCount (toForest leftChoice.word) :=
        selectResult_edges _ _ hleftHeadScore hleftTailScore
      have hrightScore : rightChoice.edges.val = forestEdgeCount (toForest rightChoice.word) :=
        selectResult_edges _ _ hrightHeadScore hrightTailScore
      have hdescendedScore : descended.edges.val = forestEdgeCount (toForest descended.word) :=
        selectResult_edges _ _ hleftScore hrightScore
      refine ⟨selectResult rooted descended,?_,?_,selectResult_edges _ _ hrootedScore hdescendedScore⟩
      · rw [isomorphism.largest_common_isomorphism]
        simp only [hrootedRun,hleftHeadRun,hleftTailRun,hrightHeadRun,hrightTailRun,bind_ok,choose_longer_correct]
        rfl
      · rw [selectResult_forest _ _ hrootedScore hdescendedScore]
        change OrderedIsoDP.longer (toForest rooted.word)
          (toForest (selectResult leftChoice rightChoice).word) = _
        rw [selectResult_forest _ _ hleftScore hrightScore]
        change OrderedIsoDP.longer (toForest rooted.word)
          (OrderedIsoDP.longer (toForest (selectResult leftHead leftTail).word)
            (toForest (selectResult rightHead rightTail).word)) = _
        rw [selectResult_forest _ _ hleftHeadScore hleftTailScore,
          selectResult_forest _ _ hrightHeadScore hrightTailScore,
          hrootedWord,hleftHeadWord,hleftTailWord,hrightHeadWord,hrightTailWord]
        simp only [toForest,OrderedIsoDP.anywhere]
termination_by forestEdgeCount (toForest left) + forestEdgeCount (toForest right)
decreasing_by
  all_goals subst_vars
  all_goals simp only [toForest,forestEdgeCount_cons,edgeCount_node]
  all_goals omega

/-- End-to-end independent connected ordered subtree optimum and exact score.
The input bounds imply success and termination of the actual translated API. -/
theorem largest_common_isomorphism_tree_correct (left right : BalancedWord)
    (hl : (toDyck left).semilength < 2^32) (hr : (toDyck right).semilength < 2^32) :
    ∃ result : CommonEmbedding,
      isomorphism.largest_common_isomorphism left right = .ok (some result) ∧
      IsMaximumIsomorphism (decodeDyck (toDyck result.word)) (decodeDyck (toDyck left)) (decodeDyck (toDyck right)) ∧
      result.edges.val = (decodeDyck (toDyck result.word)).edgeCount := by
  obtain ⟨result,hrun,hforest,hscore⟩ := largest_common_isomorphism_refines left right (by simpa only [toForest_edges] using hl) (by simpa only [toForest_edges] using hr)
  refine ⟨result,hrun,?_,?_⟩
  · rw [toTree_decode,toTree_decode,toTree_decode,hforest]
    exact OrderedIsoDP.anywhere_correct (.node (toForest left)) (.node (toForest right))
  · rw [toTree_decode]
    exact hscore

/-- Actual arbitrary-root Rust isomorphism on every independently specified
ordered-tree input under the explicit edge-count representation bounds. -/
theorem largest_common_isomorphism_of_trees (left right : Paper2004.OrderedTree)
    (hl : left.edgeCount < 2^32) (hr : right.edgeCount < 2^32) :
    ∃ result : CommonEmbedding,
      isomorphism.largest_common_isomorphism (fromDyck left.encodeDyck) (fromDyck right.encodeDyck) = .ok (some result) ∧
      IsMaximumIsomorphism (decodeDyck (toDyck result.word)) left right ∧
      result.edges.val = (decodeDyck (toDyck result.word)).edgeCount := by
  have h := largest_common_isomorphism_tree_correct (fromDyck left.encodeDyck) (fromDyck right.encodeDyck)
    (by simpa only [toDyck_fromDyck,encodeDyck_semilength] using hl)
    (by simpa only [toDyck_fromDyck,encodeDyck_semilength] using hr)
  simpa only [toDyck_fromDyck,decodeDyck_encodeDyck] using h

end SubtreeProofs.Rust.OrderedIsomorphism

end
