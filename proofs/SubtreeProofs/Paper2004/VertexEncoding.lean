module

public import SubtreeProofs.Paper2004.TokenMaximum
import Mathlib.Tactic

/-! # One-pair-per-vertex forest encoding and maximum vertex-deletion witnesses -/

@[expose] public section

namespace SubtreeProofs.Paper2004.OrderedTree

open TokenEncoding

/-- The flat vertex encoding used by a depth-first forest traversal: every
component root is enclosed, and the virtual parent contributes no pair. -/
def vertexTokens (forest : List OrderedTree) : List Bool := encoded (encodeForestDyck forest)

/-- The tree case contains its own outer pair, in addition to the paper's
edge-pair encoding. -/
theorem vertexTokens_tree (tree : OrderedTree) :
    vertexTokens [tree] = false :: (encoded tree.encodeDyck ++ [true]) := by
  simp only [vertexTokens,encodeForestDyck,add_zero]
  have h := encoded_nest_add tree.encodeDyck 0
  simpa only [add_zero,encoded_zero] using h

/-- The actual original vertices, including forest roots, each contribute two
tokens. The virtual parent is not counted. -/
@[simp] theorem vertexTokens_length (forest : List OrderedTree) :
    (vertexTokens forest).length = 2*forestVertexCount forest := by
  simp only [vertexTokens,encoded_length,encodeForestDyck_semilength,forestVertexCount_eq_edgeCount]

@[simp] theorem decodedForest_vertexCount (word : DyckWord) :
    forestVertexCount (decodeForestDyck word) = word.semilength := by
  rw [forestVertexCount_eq_edgeCount,← encodeForestDyck_semilength,encodeForestDyck_decodeForestDyck]

/-- Original retained token positions reconstruct the same independent forest,
which is maximum under vertex deletion/promotion in both original forests. -/
def MaximumVertexEmbedding (left right : List OrderedTree) (leftIndices rightIndices : List Nat) (score : Nat) : Prop :=
  ∃ common : List OrderedTree,
    IsMaximumCommonForest common left right ∧ score = forestVertexCount common ∧
    leftIndices.Sublist (List.range (vertexTokens left).length) ∧
    rightIndices.Sublist (List.range (vertexTokens right).length) ∧
    leftIndices.map (fun index => (vertexTokens left)[index]!) = vertexTokens common ∧
    rightIndices.map (fun index => (vertexTokens right)[index]!) = vertexTokens common

/-- The complete flat-token contract implies the independently specified
maximum forest with original vertex-pair tokens. This identifies both the
optimization problem and the score of the one-pair-per-vertex adapter. -/
theorem maximumTokenEmbedding_vertices (left right : List OrderedTree) (leftIndices rightIndices : List Nat) (score : Nat)
    (h : MaximumTokenEmbedding (vertexTokens left) (vertexTokens right) leftIndices rightIndices score) :
    MaximumVertexEmbedding left right leftIndices rightIndices score := by
  obtain ⟨leftWord,rightWord,common,hLeft,hRight,hl,hr,hReadLeft,hReadRight,hMaximum,hScore⟩ := h
  have hleftWord : encodeForestDyck left = leftWord := encoded_injective hLeft
  have hrightWord : encodeForestDyck right = rightWord := encoded_injective hRight
  have hm : IsMaximumCommon (.node (decodeForestDyck common)) (.node left) (.node right) := by
    simpa only [← hleftWord,← hrightWord,decodeDyck_eq_node_decodeForestDyck,decodeForestDyck_encodeForestDyck] using hMaximum
  refine ⟨decodeForestDyck common,(isMaximumCommonForest_iff_parent _ _ _).mpr hm,?_,hl,hr,?_,?_⟩
  · simpa only [decodedForest_vertexCount] using hScore
  · simpa only [vertexTokens,encodeForestDyck_decodeForestDyck] using hReadLeft
  · simpa only [vertexTokens,encodeForestDyck_decodeForestDyck] using hReadRight

end SubtreeProofs.Paper2004.OrderedTree

end
