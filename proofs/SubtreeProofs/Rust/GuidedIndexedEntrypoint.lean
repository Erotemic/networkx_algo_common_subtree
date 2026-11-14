module

public import SubtreeProofs.Rust.GuidedReconstruction
public import SubtreeProofs.Rust.IndexedOrderedEntrypoint
import Mathlib.Tactic

/-! # Actual indexed optimum using shared feasibility and guided reconstruction -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.GuidedReconstruction

open OrderedSolver IndexedOrderedSolver MemoizedOrderedSolver Paper2004.OrderedTree Paper2004.IndexedWord

/-- Every bounded original input pair returns an independently optimal indexed
contraction through the actual guided source entry point. Canonical original
numbering, the shared memoized feasibility checks and the recorded linear
witness-call bounds are supplied by the composed source refinements. -/
theorem maximum_common_embedding_indexed_guided_spec (left right : BalancedWord)
    (hl : (toDyck left).semilength < 2^32) (hr : (toDyck right).semilength < 2^32) :
    guided.maximum_common_embedding_indexed_guided left right ⦃ output => ∃ result,
      output = some result ∧ IndexedMaximum (decodeDyck (toDyck left)) (decodeDyck (toDyck right))
        (model result.left) (model result.right) result.edges.val ⦄ := by
  obtain ⟨shape,cache,hShape,hConsistent,hCache,_⟩ := memoized_common_embedding_refines left right .Empty trivial hl hr
  obtain ⟨leftInput,hLeftInput,hLeftShape,_,_,hLeftModel⟩ := number_word_refines left 0#u32 (by simpa using hl)
  obtain ⟨rightInput,hRightInput,hRightShape,_,_,hRightModel⟩ := number_word_refines right 0#u32 (by simpa using hr)
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
  unfold guided.maximum_common_embedding_indexed_guided
  simp only [hShape,bind_ok,hLeftInput,hRightInput]
  apply WP.spec_bind (reconstruct_guided_success_spec shape.word leftInput.word cache hCache hPatternBound
    (by simpa only [hLeftShape] using hl) hLeftFeasible)
  rintro output ⟨leftResult,leftWord,hOutput,hLeftWord,hLeftRetains,hLeftErasure,hLeftCache,_⟩
  subst output
  simp only [hLeftWord]
  apply WP.spec_bind (reconstruct_guided_success_spec shape.word rightInput.word leftResult.table hLeftCache hPatternBound
    (by simpa only [hRightShape] using hr) hRightFeasible)
  rintro output ⟨rightResult,rightWord,hOutput,hRightWord,hRightRetains,hRightErasure,_,_⟩
  subst output
  simp only [hRightWord]
  apply (WP.spec_ok _).mpr
  refine ⟨⟨leftWord,rightWord,shape.edges⟩,rfl,?_,?_,hLeftErasure.trans hRightErasure.symm,?_,?_⟩
  · rw [← numbered_model_canonical left leftInput hLeftModel]
    exact hLeftRetains
  · rw [← numbered_model_canonical right rightInput hRightModel]
    exact hRightRetains
  · apply longestCommonBalanced_decodes_maximum
    simpa only [encodeDyck_decodeDyck,hLeftErasure,hConsistent.1] using paperCommon_correct (toDyck left) (toDyck right)
  · rw [hLeftErasure,edgeCount_decodeDyck]
    exact hConsistent.2

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
