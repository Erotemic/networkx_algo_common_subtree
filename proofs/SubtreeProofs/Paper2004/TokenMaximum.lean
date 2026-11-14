module

public import SubtreeProofs.Paper2004.TokenReading
import Mathlib.Tactic

/-! # Independent maximum common balanced contraction with original token positions -/

@[expose] public section

namespace SubtreeProofs.Paper2004.TokenEncoding

open IndexedWord OrderedTree

/-- Concrete retained token positions spell the same balanced word in both
inputs, in original order, and attain the independent tree-contraction optimum.
The input language, token readback and optimum do not mention a parser or solver. -/
def MaximumTokenEmbedding (left right : List Bool) (leftIndices rightIndices : List Nat) (score : Nat) : Prop :=
  ∃ leftWord rightWord common : DyckWord,
    left = encoded leftWord ∧ right = encoded rightWord ∧
    leftIndices.Sublist (List.range left.length) ∧ rightIndices.Sublist (List.range right.length) ∧
    leftIndices.map (fun index => left[index]!) = encoded common ∧
    rightIndices.map (fun index => right[index]!) = encoded common ∧
    IsMaximumCommon (decodeDyck common) (decodeDyck leftWord) (decodeDyck rightWord) ∧ score = common.semilength

/-- The exact original coordinates of a retained indexed word are a sublist
of the original full token array, rather than merely indices within a bound. -/
theorem retained_token_sublist (word : DyckWord) (small : Word) (h : Retains small (numberFrom word.toTree 0)) :
    (tokenIndices (fun index => (positionPairs word.toTree 0)[index]!) small).Sublist (List.range (encoded word).length) := by
  have hs := h.tokenIndices_sublist (fun index => (positionPairs word.toTree 0)[index]!)
  simpa only [canonical_tokenIndices_zero,DyckWord.numNodes_toTree,encoded_length] using hs

/-- Expanding an independent indexed optimum at the exact input coordinate
tables supplies the full flat-token API contract. -/
theorem indexedMaximum_tokens (left right : DyckWord) (leftWitness rightWitness : Word) (score : Nat)
    (h : IndexedMaximum (decodeDyck left) (decodeDyck right) leftWitness rightWitness score) :
    MaximumTokenEmbedding (encoded left) (encoded right)
      (tokenIndices (fun index => (positionPairs left.toTree 0)[index]!) leftWitness)
      (tokenIndices (fun index => (positionPairs right.toTree 0)[index]!) rightWitness) score := by
  have hl : Retains leftWitness (numberFrom left.toTree 0) := by simpa only [canonical,encodeDyck_decodeDyck] using h.1
  have hr : Retains rightWitness (numberFrom right.toTree 0) := by simpa only [canonical,encodeDyck_decodeDyck] using h.2.1
  refine ⟨left,right,erase leftWitness,rfl,rfl,retained_token_sublist left leftWitness hl,
    retained_token_sublist right rightWitness hr,retained_readsTokens left leftWitness hl,?_,h.2.2.2.1,?_⟩
  · have hh := retained_readsTokens right rightWitness hr
    rw [ReadsTokens,← h.2.2.1] at hh
    exact hh
  · exact h.2.2.2.2.trans (edgeCount_decodeDyck _)

/-- Each side contributes exactly twice the pair score in actual tokens. -/
theorem MaximumTokenEmbedding.lengths {left right : List Bool} {leftIndices rightIndices : List Nat} {score : Nat}
    (h : MaximumTokenEmbedding left right leftIndices rightIndices score) :
    leftIndices.length = 2*score ∧ rightIndices.length = 2*score := by
  obtain ⟨_,_,common,_,_,_,_,hl,hr,_,hs⟩ := h
  have hll := congrArg List.length hl
  have hrl := congrArg List.length hr
  simpa only [List.length_map,encoded_length,hs] using And.intro hll hrl

/-- Original token positions are distinct and in bounds on both sides. -/
theorem MaximumTokenEmbedding.indices_valid {left right : List Bool} {leftIndices rightIndices : List Nat} {score : Nat}
    (h : MaximumTokenEmbedding left right leftIndices rightIndices score) :
    leftIndices.Nodup ∧ rightIndices.Nodup ∧
      (∀ index ∈ leftIndices, index < left.length) ∧ (∀ index ∈ rightIndices, index < right.length) := by
  obtain ⟨_,_,_,_,_,hl,hr,_,_,_,_⟩ := h
  exact ⟨hl.nodup List.nodup_range,hr.nodup List.nodup_range,
    fun index hi => List.mem_range.mp (hl.subset hi),fun index hi => List.mem_range.mp (hr.subset hi)⟩

end SubtreeProofs.Paper2004.TokenEncoding

end
