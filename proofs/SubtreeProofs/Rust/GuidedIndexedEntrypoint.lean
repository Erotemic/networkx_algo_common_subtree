module

public import SubtreeProofs.Rust.GuidedCacheGrowth
public import SubtreeProofs.Rust.IndexedOrderedEntrypoint
import Mathlib.Tactic

/-! # Actual indexed optimum using shared feasibility and guided reconstruction -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.GuidedReconstruction

open OrderedSolver IndexedOrderedSolver MemoizedOrderedSolver Paper2004.OrderedTree Paper2004.IndexedWord

/-- The actual instrumented optimum includes original-index witnesses, its
final sound/unique cache in the complete combined domain and a linear recorded
reconstruction-call bound. -/
structure CorrectGuided (left right : BalancedWord) (result : guided.GuidedCommonEmbedding) : Prop where
  optimum : IndexedMaximum (decodeDyck (toDyck left)) (decodeDyck (toDyck right))
    (model result.matching.left) (model result.matching.right) result.matching.edges.val
  sound : TableSound result.table
  calls_bound : result.calls.val ≤ 2*((toDyck left).semilength+(toDyck right).semilength)+2
  cache : MemoWithin (guidedDomain (toDyck left) (toDyck right) (erase (model result.matching.left))) (numericMemo result.table)

/-- The real final cache is bounded by the original shape product plus both
actual pattern/input feasibility products, including all reconstruction keys. -/
theorem CorrectGuided.cache_bound {left right : BalancedWord} {result : guided.GuidedCommonEmbedding}
    (h : CorrectGuided left right result) :
    memoLength result.table ≤
      (Paper2004.BalancedDecomposition.states (toDyck left)).card*(Paper2004.BalancedDecomposition.states (toDyck right)).card +
      (Paper2004.BalancedDecomposition.states (erase (model result.matching.left))).card*(Paper2004.BalancedDecomposition.states (toDyck left)).card +
      (Paper2004.BalancedDecomposition.states (erase (model result.matching.left))).card*(Paper2004.BalancedDecomposition.states (toDyck right)).card := by
  rw [← numericMemo_length]
  exact h.cache.length_le.trans (guidedDomain_card _ _ _)

/-- Universal bounded-input correctness of the actual cache-returning source
entry point. The cache invariant and optimum are derived from an initially
empty table; no cache certificate is a public endpoint premise. -/
theorem maximum_common_embedding_indexed_guided_with_cache_spec (left right : BalancedWord)
    (hl : (toDyck left).semilength < 2^32) (hr : (toDyck right).semilength < 2^32) :
    guided.maximum_common_embedding_indexed_guided_with_cache left right ⦃ output => ∃ result,
      output = some result ∧ CorrectGuided left right result ⦄ := by
  obtain ⟨shape,cache,hShape,hConsistent,hCache,hNumeric⟩ := memoized_common_embedding_refines left right .Empty trivial hl hr
  obtain ⟨leftInput,hLeftInput,hLeftShape,_,_,hLeftModel⟩ := number_word_refines left 0#u32 (by simpa using hl)
  obtain ⟨rightInput,hRightInput,hRightShape,_,_,hRightModel⟩ := number_word_refines right 0#u32 (by simpa using hr)
  have hWithin : MemoWithin (guidedDomain (toDyck left) (toDyck right) (toDyck shape.word)) (numericMemo cache) := by
    rw [hNumeric]
    exact (memoLcs_growth (toDyck left) (toDyck right) []).within (MemoWithin.empty _)
      (fun _ hk => hk.guided_original)
  have hFeasible := paperCommon_sound (toDyck left) (toDyck right)
  have hLeftFeasible : DyckEmbeds (toDyck shape.word) (erase (model leftInput.word)) := by
    rw [hConsistent.1,hLeftShape]
    exact hFeasible.1
  have hRightFeasible : DyckEmbeds (toDyck shape.word) (erase (model rightInput.word)) := by
    rw [hConsistent.1,hRightShape]
    exact hFeasible.2
  have hPatternBound : (toDyck shape.word).semilength < 2^32 := by
    have hsize := dyckEmbeds_semilength_le hLeftFeasible
    rw [hLeftShape] at hsize
    omega
  unfold guided.maximum_common_embedding_indexed_guided_with_cache
  simp only [hShape,bind_ok,hLeftInput,hRightInput]
  apply WP.spec_bind (WP.spec_and
    (reconstruct_guided_success_spec shape.word leftInput.word cache hCache hPatternBound
      (by simpa only [hLeftShape] using hl) hLeftFeasible)
    (reconstruct_guided_growth_spec shape.word leftInput.word cache hCache hPatternBound
      (by simpa only [hLeftShape] using hl)))
  rintro output ⟨⟨leftResult,leftWord,hOutput,hLeftWord,hLeftRetains,hLeftErasure,hLeftCache,hLeftCount⟩,hLeftGrowth⟩
  subst output
  simp only [hLeftWord]
  have hWithinLeft := hLeftGrowth.2.within hWithin (by
    intro key hk
    apply MemoDomain.guided_left
    simpa only [hLeftShape] using hk)
  apply WP.spec_bind (WP.spec_and
    (reconstruct_guided_success_spec shape.word rightInput.word leftResult.table hLeftCache hPatternBound
      (by simpa only [hRightShape] using hr) hRightFeasible)
    (reconstruct_guided_growth_spec shape.word rightInput.word leftResult.table hLeftCache hPatternBound
      (by simpa only [hRightShape] using hr)))
  rintro output ⟨⟨rightResult,rightWord,hOutput,hRightWord,hRightRetains,hRightErasure,hRightCache,hRightCount⟩,hRightGrowth⟩
  subst output
  simp only [hRightWord]
  have hWithinRight := hRightGrowth.2.within hWithinLeft (by
    intro key hk
    apply MemoDomain.guided_right
    simpa only [hRightShape] using hk)
  rw [hLeftShape] at hLeftCount
  rw [hRightShape] at hRightCount
  obtain ⟨calls,hCalls,hCallsValue⟩ := checked_add64_success leftResult.calls rightResult.calls (by omega)
  simp only [lift,hCalls,bind_ok]
  apply (WP.spec_ok _).mpr
  refine ⟨⟨⟨leftWord,rightWord,shape.edges⟩,rightResult.table,calls⟩,rfl,?_,hRightCache,?_,?_⟩
  · refine ⟨?_,?_,hLeftErasure.trans hRightErasure.symm,?_,?_⟩
    · rw [← numbered_model_canonical left leftInput hLeftModel]
      exact hLeftRetains
    · rw [← numbered_model_canonical right rightInput hRightModel]
      exact hRightRetains
    · apply longestCommonBalanced_decodes_maximum
      simpa only [encodeDyck_decodeDyck,hLeftErasure,hConsistent.1] using paperCommon_correct (toDyck left) (toDyck right)
    · rw [hLeftErasure,edgeCount_decodeDyck]
      exact hConsistent.2
  · change calls.val ≤ _
    omega
  · change MemoWithin (guidedDomain (toDyck left) (toDyck right) (erase (model leftWord))) (numericMemo rightResult.table)
    rw [hLeftErasure]
    exact hWithinRight

/-- The ordinary actual indexed API discards the proved instrumentation and
returns the same independently maximum original-index witness. -/
theorem maximum_common_embedding_indexed_guided_spec (left right : BalancedWord)
    (hl : (toDyck left).semilength < 2^32) (hr : (toDyck right).semilength < 2^32) :
    guided.maximum_common_embedding_indexed_guided left right ⦃ output => ∃ result,
      output = some result ∧ IndexedMaximum (decodeDyck (toDyck left)) (decodeDyck (toDyck right))
        (model result.left) (model result.right) result.edges.val ⦄ := by
  unfold guided.maximum_common_embedding_indexed_guided
  apply WP.spec_bind (maximum_common_embedding_indexed_guided_with_cache_spec left right hl hr)
  rintro output ⟨result,hOutput,hCorrect⟩
  subst output
  apply (WP.spec_ok _).mpr
  exact ⟨result.matching,rfl,hCorrect.optimum⟩

/-- The guided indexed API covers every independent ordered tree pair under
the same edge bounds as the reference entry point. -/
theorem maximum_common_embedding_indexed_guided_of_trees (left right : Paper2004.OrderedTree)
    (hl : left.edgeCount < 2^32) (hr : right.edgeCount < 2^32) :
    guided.maximum_common_embedding_indexed_guided (fromDyck left.encodeDyck) (fromDyck right.encodeDyck) ⦃ output => ∃ result,
      output = some result ∧ IndexedMaximum left right (model result.left) (model result.right) result.edges.val ⦄ := by
  simpa only [toDyck_fromDyck,decodeDyck_encodeDyck] using
    maximum_common_embedding_indexed_guided_spec (fromDyck left.encodeDyck) (fromDyck right.encodeDyck)
      (by simpa only [toDyck_fromDyck,encodeDyck_semilength] using hl)
      (by simpa only [toDyck_fromDyck,encodeDyck_semilength] using hr)

end SubtreeProofs.Rust.GuidedReconstruction

end
