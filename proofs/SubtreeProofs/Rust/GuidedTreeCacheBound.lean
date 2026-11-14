module

public import SubtreeProofs.Rust.GuidedIndexedEntrypoint
public import SubtreeProofs.Paper2004.ContractionMeasures
import Mathlib.Tactic

/-! # Actual guided-cache bound in the original tree sizes, depths and true leaves -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.GuidedReconstruction

open OrderedSolver IndexedOrderedSolver MemoizedOrderedSolver Paper2004.OrderedTree Paper2004.IndexedWord

/-- The actual guided cache has at most three times the original inputs'
repaired depth/leaf state-product bound. The output pattern contributes no
independent parameter: it is an actual common contracted tree. -/
theorem CorrectGuided.original_cache_bound {left right : BalancedWord} {result : guided.GuidedCommonEmbedding}
    (h : CorrectGuided left right result) :
    memoLength result.table ≤ 3*decompositionBound (decodeDyck (toDyck left))*decompositionBound (decodeDyck (toDyck right)) := by
  have hl : (Paper2004.BalancedDecomposition.states (toDyck left)).card ≤ decompositionBound (decodeDyck (toDyck left)) := by
    simpa only [encodeDyck_decodeDyck] using states_card_le_decompositionBound (decodeDyck (toDyck left))
  have hr : (Paper2004.BalancedDecomposition.states (toDyck right)).card ≤ decompositionBound (decodeDyck (toDyck right)) := by
    simpa only [encodeDyck_decodeDyck] using states_card_le_decompositionBound (decodeDyck (toDyck right))
  have hp : (Paper2004.BalancedDecomposition.states (erase (model result.matching.left))).card ≤
      decompositionBound (decodeDyck (erase (model result.matching.left))) := by
    simpa only [encodeDyck_decodeDyck] using states_card_le_decompositionBound (decodeDyck (erase (model result.matching.left)))
  have hMaximum := h.optimum.2.2.2.1
  have hpl := hp.trans (embeds_decompositionBound_le hMaximum.1.1)
  have hpr := hp.trans (embeds_decompositionBound_le hMaximum.1.2)
  have hmain := Nat.mul_le_mul hl hr
  have hleft := Nat.mul_le_mul hpr hl
  have hright := Nat.mul_le_mul hpl hr
  have hcache := h.cache_bound
  nlinarith

/-- Every actual bounded source input pair succeeds with the complete indexed
optimum/counter/cache contract and the cache bound in original tree parameters. -/
theorem maximum_common_embedding_indexed_guided_original_cache_spec (left right : BalancedWord)
    (hl : (toDyck left).semilength < 2^32) (hr : (toDyck right).semilength < 2^32) :
    guided.maximum_common_embedding_indexed_guided_with_cache left right ⦃ output => ∃ result,
      output = some result ∧ CorrectGuided left right result ∧
      memoLength result.table ≤ 3*decompositionBound (decodeDyck (toDyck left))*decompositionBound (decodeDyck (toDyck right)) ⦄ := by
  apply WP.spec_mono (maximum_common_embedding_indexed_guided_with_cache_spec left right hl hr)
  rintro output ⟨result,hOutput,hCorrect⟩
  exact ⟨result,hOutput,hCorrect,hCorrect.original_cache_bound⟩

/-- Original independent trees instantiate the actual source endpoint with
only their real edge bounds. The repaired state-product expression uses their
own edge counts, vertex depths and actual leaves. -/
theorem maximum_common_embedding_indexed_guided_cache_of_trees (left right : Paper2004.OrderedTree)
    (hl : left.edgeCount < 2^32) (hr : right.edgeCount < 2^32) :
    guided.maximum_common_embedding_indexed_guided_with_cache (fromDyck left.encodeDyck) (fromDyck right.encodeDyck) ⦃ output => ∃ result,
      output = some result ∧ CorrectGuided (fromDyck left.encodeDyck) (fromDyck right.encodeDyck) result ∧
      memoLength result.table ≤ 3*decompositionBound left*decompositionBound right ⦄ := by
  simpa only [toDyck_fromDyck,decodeDyck_encodeDyck] using
    maximum_common_embedding_indexed_guided_original_cache_spec (fromDyck left.encodeDyck) (fromDyck right.encodeDyck)
      (by simpa only [toDyck_fromDyck,encodeDyck_semilength] using hl)
      (by simpa only [toDyck_fromDyck,encodeDyck_semilength] using hr)

end SubtreeProofs.Rust.GuidedReconstruction

end
