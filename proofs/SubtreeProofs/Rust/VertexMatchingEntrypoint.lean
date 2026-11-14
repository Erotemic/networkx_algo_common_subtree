module

public import SubtreeProofs.Rust.TokenMatchingEntrypoint
public import SubtreeProofs.Paper2004.VertexEncoding
import Mathlib.Tactic

/-! # Actual Rust optimum under the one-pair-per-vertex forest convention -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.TokenMatching

open Paper2004.OrderedTree

/-- The actual flat Rust API returns an independently maximum vertex-deletion
forest with the exact original vertex-pair token positions. The representation
hypotheses specify only original input arrays, and the pair bounds count actual
forest vertices, including component roots. -/
theorem maximum_common_token_embedding_of_forests (left right : Slice Bool)
    (leftForest rightForest : List Paper2004.OrderedTree)
    (hl : left.val = vertexTokens leftForest) (hr : right.val = vertexTokens rightForest)
    (hlb : forestVertexCount leftForest < 2^32) (hrb : forestVertexCount rightForest < 2^32) :
    token_matching.maximum_common_token_embedding left right ⦃ output => ∃ result,
      output = core.result.Result.Ok result ∧
      MaximumVertexEmbedding leftForest rightForest (tokenView result.left) (tokenView result.right) result.edges.val ⦄ := by
  have hla : TokenParser.Admissible left := ⟨encodeForestDyck leftForest,hl,by
    simpa only [encodeForestDyck_semilength,forestVertexCount_eq_edgeCount] using hlb⟩
  have hra : TokenParser.Admissible right := ⟨encodeForestDyck rightForest,hr,by
    simpa only [encodeForestDyck_semilength,forestVertexCount_eq_edgeCount] using hrb⟩
  apply WP.spec_mono (maximum_common_token_embedding_spec left right hla hra)
  rintro output ⟨result,hOutput,hMaximum⟩
  refine ⟨result,hOutput,?_⟩
  rw [hl,hr] at hMaximum
  exact maximumTokenEmbedding_vertices leftForest rightForest _ _ _ hMaximum

end SubtreeProofs.Rust.TokenMatching

end
