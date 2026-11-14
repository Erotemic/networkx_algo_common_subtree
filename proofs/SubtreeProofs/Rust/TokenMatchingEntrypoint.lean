module

public import SubtreeProofs.Rust.TokenEmission
public import SubtreeProofs.Rust.TokenParserEntrypoint
public import SubtreeProofs.Rust.IndexedOrderedEntrypoint
public import SubtreeProofs.Paper2004.TokenMaximum
import Mathlib.Tactic

/-! # Actual flat-token maximum common contraction with original token witnesses -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.TokenMatching

open OrderedSolver IndexedOrderedSolver TokenParser Paper2004.TokenEncoding Paper2004.IndexedWord

/-- Exact parser coordinates and actual retention supply every emitter bound,
including the capacity for both endpoints of every surviving pair. -/
theorem emit_parsed_spec (input : Slice Bool) (parsed : tokens.ParsedForest) (hc : CorrectParsed input parsed)
    (word : indexed.IndexedWord) (hr : Retains (model word) (numberFrom (toDyck parsed.word).toTree 0)) :
    token_matching.emit_tokens word (alloc.vec.Vec.deref parsed.positions) (alloc.vec.Vec.new Usize) ⦃ result =>
      ∃ emitted, result = core.result.Result.Ok emitted ∧
        tokenView emitted = tokenIndices (fun index => (positionPairs (toDyck parsed.word).toTree 0)[index]!) (model word) ⦄ := by
  have hcount : parsed.positions.length = (toDyck parsed.word).semilength := by
    have hh := congrArg List.length hc.positions_exact
    simpa only [coordinateView_length,positionPairs_length,DyckWord.numNodes_toTree] using hh
  have hcoordCount : (alloc.vec.Vec.deref parsed.positions).length = (toDyck parsed.word).semilength := by
    simpa only [alloc.vec.Vec.deref,Slice.from_val,Slice.length,alloc.vec.Vec.length] using hcount
  have hid : ∀ index ∈ indices (model word), index < (alloc.vec.Vec.deref parsed.positions).length := by
    intro index hi
    rw [hcoordCount]
    exact hr.index_lt (toDyck parsed.word).semilength
      (by simp only [indices_numberFrom,DyckWord.numNodes_toTree,List.range_eq_range']) index hi
  have hsub := retained_token_sublist (toDyck parsed.word) (model word) hr
  have hlen := hsub.length_le
  simp only [tokenIndices_length,List.length_range] at hlen
  have hcapacity : (alloc.vec.Vec.new Usize).length+2*(model word).numNodes ≤ Usize.max := by
    have hinputBound := input.property
    rw [hc.encoded_input] at hinputBound
    simpa only [alloc.vec.Vec.length,alloc.vec.Vec.new,alloc.vec.Vec.from_val,List.length_nil,Nat.zero_add] using hlen.trans hinputBound
  apply WP.spec_mono (emit_tokens_spec word (alloc.vec.Vec.deref parsed.positions) (alloc.vec.Vec.new Usize) hid hcapacity)
  rintro result ⟨emitted,hResult,hEmitted⟩
  refine ⟨emitted,hResult,?_⟩
  have hv : (alloc.vec.Vec.deref parsed.positions).val.map positionValue = positionPairs (toDyck parsed.word).toTree 0 := by
    simpa only [alloc.vec.Vec.deref,Slice.from_val,coordinateView] using hc.positions_exact
  simpa only [hv,tokenView,alloc.vec.Vec.new,alloc.vec.Vec.from_val,List.map_nil,List.nil_append] using hEmitted

/-- Every independently admitted input pair returns a maximum balanced
contraction and concrete retained token positions from each original input.
The indexed optimizer, parser, casts and output emission are actual source calls. -/
theorem maximum_common_token_embedding_spec (left right : Slice Bool) (hl : Admissible left) (hr : Admissible right) :
    token_matching.maximum_common_token_embedding left right ⦃ output => ∃ result,
      output = core.result.Result.Ok result ∧
      MaximumTokenEmbedding left.val right.val (tokenView result.left) (tokenView result.right) result.edges.val ⦄ := by
  unfold token_matching.maximum_common_token_embedding
  apply WP.spec_bind (parse_balanced_tokens_spec left hl)
  rintro leftResult ⟨leftParsed,hLeftResult,hLeft⟩
  subst leftResult
  apply WP.spec_bind (parse_balanced_tokens_spec right hr)
  rintro rightResult ⟨rightParsed,hRightResult,hRight⟩
  subst rightResult
  obtain ⟨matching,hMatching,hMaximum⟩ := maximum_common_embedding_indexed_correct leftParsed.word rightParsed.word hLeft.pair_bound hRight.pair_bound
  simp only [hMatching,bind_ok]
  have hlr : Retains (model matching.left) (numberFrom (toDyck leftParsed.word).toTree 0) := by
    simpa only [canonical,Paper2004.OrderedTree.encodeDyck_decodeDyck] using hMaximum.1
  have hrr : Retains (model matching.right) (numberFrom (toDyck rightParsed.word).toTree 0) := by
    simpa only [canonical,Paper2004.OrderedTree.encodeDyck_decodeDyck] using hMaximum.2.1
  apply WP.spec_bind (emit_parsed_spec left leftParsed hLeft matching.left hlr)
  rintro leftOutput ⟨leftTokens,hLeftOutput,hLeftTokens⟩
  subst leftOutput
  apply WP.spec_bind (emit_parsed_spec right rightParsed hRight matching.right hrr)
  rintro rightOutput ⟨rightTokens,hRightOutput,hRightTokens⟩
  subst rightOutput
  simp only [WP.spec_ok]
  refine ⟨⟨leftTokens,rightTokens,matching.edges⟩,rfl,?_⟩
  simpa only [hLeft.encoded_input,hRight.encoded_input,hLeftTokens,hRightTokens] using
    indexedMaximum_tokens (toDyck leftParsed.word) (toDyck rightParsed.word) (model matching.left) (model matching.right) matching.edges.val hMaximum

/-- Every represented input pair either succeeds on the independently admitted
balanced domain or reports the excluded input side, with left-input precedence.
Internal solver/index errors are unreachable. -/
def ResultSpec (left right : Slice Bool)
    (output : core.result.Result token_matching.TokenCommonEmbedding token_matching.TokenMatchingError) : Prop :=
  match output with
  | .Ok result => Admissible left ∧ Admissible right ∧
      MaximumTokenEmbedding left.val right.val (tokenView result.left) (tokenView result.right) result.edges.val
  | .Err (.LeftInput _) => ¬ Admissible left
  | .Err (.RightInput _) => Admissible left ∧ ¬ Admissible right
  | .Err _ => False

/-- Total correctness of the actual flat-token Rust API on every represented
input pair, including malformed or oversized inputs. Success has exact original
token readback and independent global optimality, without an input certificate. -/
theorem maximum_common_token_embedding_total_spec (left right : Slice Bool) :
    token_matching.maximum_common_token_embedding left right ⦃ output => ResultSpec left right output ⦄ := by
  classical
  by_cases hl : Admissible left
  · by_cases hr : Admissible right
    · apply WP.spec_mono (maximum_common_token_embedding_spec left right hl hr)
      rintro output ⟨result,hOutput,hCorrect⟩
      subst output
      exact ⟨hl,hr,hCorrect⟩
    · unfold token_matching.maximum_common_token_embedding
      apply WP.spec_bind (parse_balanced_tokens_spec left hl)
      rintro leftOutput ⟨leftParsed,hLeftOutput,_⟩
      subst leftOutput
      apply WP.spec_bind (parse_balanced_tokens_total_spec right)
      intro rightOutput hRight
      cases rightOutput with
      | Err error =>
        simp only [WP.spec_ok,ResultSpec]
        exact ⟨hl,hRight⟩
      | Ok parsed => exact False.elim (hr hRight.1)
  · unfold token_matching.maximum_common_token_embedding
    apply WP.spec_bind (parse_balanced_tokens_total_spec left)
    intro leftOutput hLeft
    cases leftOutput with
    | Err error =>
      simp only [WP.spec_ok,ResultSpec]
      exact hLeft
    | Ok parsed => exact False.elim (hl hLeft.1)

end SubtreeProofs.Rust.TokenMatching

end
