module

public import SubtreeProofs.Rust.IndexedIsomorphismReconstruction
public import SubtreeProofs.Paper2004.IndexedIsomorphism
import Mathlib.Tactic

/-! # Actual complete original-index isomorphism reference API -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.IndexedIsomorphism

open IndexedOrderedSolver OrderedSolver OrderedIsomorphism Paper2004.OrderedTree

theorem structural_optimum (left right : BalancedWord) (rooted : Bool)
    (hl : (toDyck left).semilength < 2^32) (hr : (toDyck right).semilength < 2^32) :
    ∃ shape, (if rooted then isomorphism.rooted_common_isomorphism left right else
      isomorphism.largest_common_isomorphism left right) = .ok (some shape) ∧
      Paper2004.IndexedIso.MaximumShape rooted (decodeDyck (toDyck shape.word))
        (decodeDyck (toDyck left)) (decodeDyck (toDyck right)) ∧
      shape.edges.val = (toDyck shape.word).semilength := by
  cases rooted with
  | true =>
    obtain ⟨shape,hRun,hMaximum,hScore⟩ := rooted_common_isomorphism_tree_correct left right hl hr
    exact ⟨shape,hRun,hMaximum,hScore.trans (edgeCount_decodeDyck _)⟩
  | false =>
    obtain ⟨shape,hRun,hMaximum,hScore⟩ := largest_common_isomorphism_tree_correct left right hl hr
    exact ⟨shape,hRun,hMaximum,hScore.trans (edgeCount_decodeDyck _)⟩

theorem reconstruct_success (pattern : BalancedWord) (input : indexed.IndexedWord) (rooted : Bool)
    (h : if rooted then ForestPrunes (toForest pattern) (forest input) else
      IsomorphicSubtree (.node (toForest pattern)) (.node (forest input))) :
    ∃ result, (if rooted then indexed_isomorphism.reconstruct_rooted_isomorphism pattern input else
      indexed_isomorphism.reconstruct_any_isomorphism pattern input) = .ok (some result) ∧
      Paper2004.IndexedIso.Prunes rooted (model result) (model input) ∧ forest result = toForest pattern := by
  cases rooted with
  | true => exact reconstruct_rooted_success pattern input h
  | false => exact reconstruct_any_success pattern input h

/-- Canonical original numbering, complete source reconstruction and the
independent structural optimum compose without a supplied output certificate.
The reference remains exponential and distinct from the optimized backend. -/
theorem maximum_common_isomorphism_indexed_spec (left right : BalancedWord) (rooted : Bool)
    (hl : (toDyck left).semilength < 2^32) (hr : (toDyck right).semilength < 2^32) :
    ∃ result : indexed.IndexedCommonEmbedding,
      indexed_isomorphism.maximum_common_isomorphism_indexed left right rooted = .ok (some result) ∧
      Paper2004.IndexedIso.Maximum rooted (toDyck left) (toDyck right)
        (model result.left) (model result.right) result.edges.val := by
  obtain ⟨shape,hShapeRun,hMaximum,hScore⟩ := structural_optimum left right rooted hl hr
  obtain ⟨leftInput,hLeftRun,hLeftShape,_,_,hLeftModel⟩ := number_word_refines left 0#u32 (by simpa using hl)
  obtain ⟨rightInput,hRightRun,hRightShape,_,_,hRightModel⟩ := number_word_refines right 0#u32 (by simpa using hr)
  have hLeftForest : forest leftInput.word = toForest left := by rw [forest_decode,hLeftShape]; exact (toForest_decode left).symm
  have hRightForest : forest rightInput.word = toForest right := by rw [forest_decode,hRightShape]; exact (toForest_decode right).symm
  have hLeftFeasible : if rooted then ForestPrunes (toForest shape.word) (forest leftInput.word) else
      IsomorphicSubtree (.node (toForest shape.word)) (.node (forest leftInput.word)) := by
    rw [hLeftForest]
    cases rooted with
    | false => simpa only [Bool.false_eq_true,↓reduceIte,toTree_decode] using hMaximum.1.1
    | true =>
      have hTree := hMaximum.1.1
      rw [toTree_decode,toTree_decode] at hTree
      exact hTree.children
  have hRightFeasible : if rooted then ForestPrunes (toForest shape.word) (forest rightInput.word) else
      IsomorphicSubtree (.node (toForest shape.word)) (.node (forest rightInput.word)) := by
    rw [hRightForest]
    cases rooted with
    | false => simpa only [Bool.false_eq_true,↓reduceIte,toTree_decode] using hMaximum.1.2
    | true =>
      have hTree := hMaximum.1.2
      rw [toTree_decode,toTree_decode] at hTree
      exact hTree.children
  obtain ⟨leftWitness,hLeftWitness,hLeftPrunes,hLeftForestOut⟩ := reconstruct_success shape.word leftInput.word rooted hLeftFeasible
  obtain ⟨rightWitness,hRightWitness,hRightPrunes,hRightForestOut⟩ := reconstruct_success shape.word rightInput.word rooted hRightFeasible
  have hLeftOriginal : model leftInput.word = Paper2004.IndexedWord.numberFrom (toDyck left).toTree 0 := by
    simpa only [sourceShape_toTree,UScalar.ofNatCore_val_eq] using hLeftModel
  have hRightOriginal : model rightInput.word = Paper2004.IndexedWord.numberFrom (toDyck right).toTree 0 := by
    simpa only [sourceShape_toTree,UScalar.ofNatCore_val_eq] using hRightModel
  have hLeftErase : Paper2004.IndexedWord.erase (model leftWitness) = toDyck shape.word := by
    rw [← forest_encode,hLeftForestOut,toForest_encode]
  have hRightErase : Paper2004.IndexedWord.erase (model rightWitness) = toDyck shape.word := by
    rw [← forest_encode,hRightForestOut,toForest_encode]
  refine ⟨⟨leftWitness,rightWitness,shape.edges⟩,?_,?_,?_,hLeftErase.trans hRightErase.symm,?_,?_⟩
  · unfold indexed_isomorphism.maximum_common_isomorphism_indexed
    simp only [hShapeRun,hLeftRun,hRightRun,hLeftWitness,hRightWitness,bind_ok]
  · simpa only [hLeftOriginal] using hLeftPrunes
  · simpa only [hRightOriginal] using hRightPrunes
  · rw [hLeftErase]
    exact hMaximum
  · rw [hLeftErase]
    exact hScore

end SubtreeProofs.Rust.IndexedIsomorphism

end
