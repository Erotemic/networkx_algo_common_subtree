module

public import SubtreeProofs.Rust.IndexedReconstruction
public import SubtreeProofs.Rust.IndexedWordNumbering
public import SubtreeProofs.Rust.MemoizedOrderedSolver
import Mathlib.Tactic

/-!
# Actual public indexed maximum common contraction

The actual memoized shape optimum, canonical original-input numbering and
complete indexed reconstruction compose to an independently maximum tree
with original pair identities in both inputs. The index specification fixes
the exact canonical original, rather than assuming a range or an arbitrary
numbered witness from the caller.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.IndexedOrderedSolver

open OrderedSolver Paper2004.OrderedTree Paper2004.IndexedWord

/-- The exact source-numbered model is the independent original tree's
canonical index representation, through the established two-sided encoding. -/
theorem numbered_model_canonical (word : BalancedWord) (result : indexed.NumberedWord)
    (h : model result.word = numberFrom (sourceShape word) (0#u32).val) :
    model result.word = canonical (decodeDyck (toDyck word)) := by
  rw [h,sourceShape_toTree]
  simp only [canonical,encodeDyck_decodeDyck,UScalar.ofNatCore_val_eq]

/-- Every admitted represented input pair succeeds with an independently
maximum common contracted tree, exact score, and actual canonical original
input pair identities. No optimum or reconstruction certificate is supplied. -/
theorem maximum_common_embedding_indexed_correct (left right : BalancedWord)
    (hl : (toDyck left).semilength < 2^32) (hr : (toDyck right).semilength < 2^32) :
    ∃ result : indexed.IndexedCommonEmbedding,
      indexed.maximum_common_embedding_indexed left right = .ok (some result) ∧
      IndexedMaximum (decodeDyck (toDyck left)) (decodeDyck (toDyck right))
        (model result.left) (model result.right) result.edges.val := by
  obtain ⟨shape,hShapeRun,hMaximum,hScore⟩ := MemoizedOrderedSolver.maximum_common_embedding_correct left right hl hr
  obtain ⟨leftInput,hLeftRun,hLeftShape,_,_,hLeftModel⟩ := number_word_refines left 0#u32 (by simpa using hl)
  obtain ⟨rightInput,hRightRun,hRightShape,_,_,hRightModel⟩ := number_word_refines right 0#u32 (by simpa using hr)
  have hLeftFeasible : DyckEmbeds (toDyck shape.word) (erase (model leftInput.word)) := by
    rw [hLeftShape]
    simpa only [encodeDyck_decodeDyck] using embeds_encodeDyck hMaximum.1.1
  have hRightFeasible : DyckEmbeds (toDyck shape.word) (erase (model rightInput.word)) := by
    rw [hRightShape]
    simpa only [encodeDyck_decodeDyck] using embeds_encodeDyck hMaximum.1.2
  obtain ⟨leftWitness,hLeftWitness,hLeftRetains,hLeftErasure⟩ := reconstruct_embedding_success shape.word leftInput.word hLeftFeasible
  obtain ⟨rightWitness,hRightWitness,hRightRetains,hRightErasure⟩ := reconstruct_embedding_success shape.word rightInput.word hRightFeasible
  have hLeftOriginal := numbered_model_canonical left leftInput hLeftModel
  have hRightOriginal := numbered_model_canonical right rightInput hRightModel
  refine ⟨⟨leftWitness,rightWitness,shape.edges⟩,?_,?_,?_,?_,?_,?_⟩
  · unfold indexed.maximum_common_embedding_indexed
    simp only [hShapeRun,hLeftRun,hRightRun,hLeftWitness,hRightWitness,bind_ok]
  · rw [← hLeftOriginal]
    exact hLeftRetains
  · rw [← hRightOriginal]
    exact hRightRetains
  · exact hLeftErasure.trans hRightErasure.symm
  · rw [hLeftErasure]
    exact hMaximum
  · rw [hLeftErasure]
    exact hScore

/-- Every pair of independently specified ordered trees under the u32 edge
bounds is covered by the actual public indexed Rust entry point. The returned
matching pair identities are genuine original zero-based edge positions. -/
theorem maximum_common_embedding_indexed_of_trees (left right : Paper2004.OrderedTree)
    (hl : left.edgeCount < 2^32) (hr : right.edgeCount < 2^32) :
    ∃ result : indexed.IndexedCommonEmbedding,
      indexed.maximum_common_embedding_indexed (fromDyck left.encodeDyck) (fromDyck right.encodeDyck) = .ok (some result) ∧
      IndexedMaximum left right (model result.left) (model result.right) result.edges.val := by
  have h := maximum_common_embedding_indexed_correct (fromDyck left.encodeDyck) (fromDyck right.encodeDyck)
    (by simpa only [toDyck_fromDyck,encodeDyck_semilength] using hl)
    (by simpa only [toDyck_fromDyck,encodeDyck_semilength] using hr)
  simpa only [toDyck_fromDyck,decodeDyck_encodeDyck] using h

/-- An actual public indexed optimum has unique original indices in bounds
and precisely one original index on each side per scored output edge. -/
theorem maximum_common_embedding_indexed_indices (left right : Paper2004.OrderedTree)
    (hl : left.edgeCount < 2^32) (hr : right.edgeCount < 2^32) :
    ∃ result : indexed.IndexedCommonEmbedding,
      indexed.maximum_common_embedding_indexed (fromDyck left.encodeDyck) (fromDyck right.encodeDyck) = .ok (some result) ∧
      IndexedMaximum left right (model result.left) (model result.right) result.edges.val ∧
      (indices (model result.left)).Nodup ∧ (indices (model result.right)).Nodup ∧
      (∀ index ∈ indices (model result.left), index < left.edgeCount) ∧
      (∀ index ∈ indices (model result.right), index < right.edgeCount) ∧
      (indices (model result.left)).length = result.edges.val ∧ (indices (model result.right)).length = result.edges.val := by
  obtain ⟨result,hrun,hcorrect⟩ := maximum_common_embedding_indexed_of_trees left right hl hr
  obtain ⟨hlNodup,hrNodup,hlBound,hrBound⟩ := hcorrect.indices_valid
  obtain ⟨hlLength,hrLength⟩ := hcorrect.indices_length
  exact ⟨result,hrun,hcorrect,hlNodup,hrNodup,hlBound,hrBound,hlLength,hrLength⟩

end SubtreeProofs.Rust.IndexedOrderedSolver

end
