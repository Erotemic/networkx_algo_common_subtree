module

public import SubtreeProofs.Rust.GuidedTreeCacheBound
import Mathlib.Tactic

/-! # Owned structural word payload in the actual guided memo -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.GuidedReconstruction

open OrderedSolver IndexedOrderedSolver MemoizedOrderedSolver Paper2004.OrderedTree Paper2004.IndexedWord

/-- Structural constructors in an owned source balanced-word value, counting
both Pair and Empty. This is a value-size metric, not an allocator-byte counter. -/
def wordNodes : BalancedWord → Nat
  | .Empty => 1
  | .Pair head tail => 1+wordNodes head+wordNodes tail

@[simp] theorem wordNodes_eq (word : BalancedWord) : wordNodes word = 2*(toDyck word).semilength+1 := by
  induction word with
  | Empty => rfl
  | Pair head tail ihHead ihTail =>
    simp only [wordNodes,toDyck,DyckWord.semilength_add,DyckWord.semilength_nest,ihHead,ihTail]
    omega

/-- Every actual cache entry owns two full key words and one full result word.
Their constructors are all counted, including repeated values in different
records. The separately counted table links and record structs are excluded. -/
def memoWordNodes : RustMemo → Nat
  | .Empty => 0
  | .Entry entry rest => wordNodes entry.left+wordNodes entry.right+wordNodes entry.result.word+memoWordNodes rest

/-- Sound memo values cannot exceed either key, so a combined key budget also
bounds the actual owned result payload in every stored record. -/
theorem memoWordNodes_bound (table : RustMemo) (leftSize rightSize : Nat) (hs : TableSound table)
    (hk : ∀ entry ∈ numericMemo table,
      entry.1.1.semilength+entry.1.2.semilength ≤ leftSize+rightSize ∧
      min entry.1.1.semilength entry.1.2.semilength ≤ min leftSize rightSize) :
    memoWordNodes table ≤ (2*(leftSize+rightSize+min leftSize rightSize)+3)*memoLength table := by
  induction table with
  | Empty => simp only [memoWordNodes,memoLength,Nat.mul_zero,le_refl]
  | Entry entry rest ih =>
    have hkey := hk ((toDyck entry.left,toDyck entry.right),entry.result.edges.val) (by simp only [numericMemo,List.mem_cons]; exact Or.inl True.intro)
    have hrest := ih hs.2 (fun entry he => hk entry (List.mem_cons_of_mem _ he))
    have hl : (toDyck entry.result.word).semilength ≤ (toDyck entry.left).semilength := by
      rw [hs.1.1]
      exact dyckEmbeds_semilength_le (paperCommon_sound _ _).1
    have hr : (toDyck entry.result.word).semilength ≤ (toDyck entry.right).semilength := by
      rw [hs.1.1]
      exact dyckEmbeds_semilength_le (paperCommon_sound _ _).2
    have he : wordNodes entry.left+wordNodes entry.right+wordNodes entry.result.word ≤
        2*(leftSize+rightSize+min leftSize rightSize)+3 := by
      simp only [wordNodes_eq]
      dsimp only at hkey
      omega
    simp only [memoWordNodes,memoLength]
    nlinarith

/-- The real final guided table's owned key/result constructors have a linear
original-input-size factor per stored record. This makes the representation
factor explicit instead of equating record count with memory size. -/
theorem CorrectGuided.payload_bound {left right : BalancedWord} {result : guided.GuidedCommonEmbedding}
    (h : CorrectGuided left right result) :
    memoWordNodes result.table ≤
      (2*((toDyck left).semilength+(toDyck right).semilength+min (toDyck left).semilength (toDyck right).semilength)+3)*memoLength result.table := by
  have hm := h.optimum.2.2.2.1
  have hl := embeds_edgeCount_le hm.1.1
  have hr := embeds_edgeCount_le hm.1.2
  simp only [edgeCount_decodeDyck] at hl hr
  apply memoWordNodes_bound result.table _ _ h.sound
  intro entry he
  exact guidedDomain_lengths hl hr entry.1 (h.cache.keys entry he)

/-- The final actual owned-word payload is bounded entirely by original tree
sizes, depths and true leaves. This concerns the returned table snapshot;
intermediate allocations and lookup/copy work are separate costs. -/
theorem CorrectGuided.original_payload_bound {left right : BalancedWord} {result : guided.GuidedCommonEmbedding}
    (h : CorrectGuided left right result) :
    memoWordNodes result.table ≤
      (2*((toDyck left).semilength+(toDyck right).semilength+min (toDyck left).semilength (toDyck right).semilength)+3)*
        (3*decompositionBound (decodeDyck (toDyck left))*decompositionBound (decodeDyck (toDyck right))) :=
  h.payload_bound.trans (Nat.mul_le_mul_left _ h.original_cache_bound)

/-- Every original tree pair below the edge bounds returns an actual maximum
indexed result whose final owned cache words obey the original-input payload
bound. The cache itself is produced by the Rust source call. -/
theorem maximum_common_embedding_indexed_guided_payload_of_trees (left right : Paper2004.OrderedTree)
    (hl : left.edgeCount < 2^32) (hr : right.edgeCount < 2^32) :
    guided.maximum_common_embedding_indexed_guided_with_cache (fromDyck left.encodeDyck) (fromDyck right.encodeDyck) ⦃ output => ∃ result,
      output = some result ∧ CorrectGuided (fromDyck left.encodeDyck) (fromDyck right.encodeDyck) result ∧
      memoWordNodes result.table ≤ (2*(left.edgeCount+right.edgeCount+min left.edgeCount right.edgeCount)+3)*
        (3*decompositionBound left*decompositionBound right) ⦄ := by
  apply WP.spec_mono (maximum_common_embedding_indexed_guided_with_cache_spec (fromDyck left.encodeDyck) (fromDyck right.encodeDyck)
    (by simpa only [toDyck_fromDyck,encodeDyck_semilength] using hl)
    (by simpa only [toDyck_fromDyck,encodeDyck_semilength] using hr))
  rintro output ⟨result,hOutput,hCorrect⟩
  refine ⟨result,hOutput,hCorrect,?_⟩
  simpa only [toDyck_fromDyck,encodeDyck_semilength,decodeDyck_encodeDyck] using hCorrect.original_payload_bound

end SubtreeProofs.Rust.GuidedReconstruction

end
