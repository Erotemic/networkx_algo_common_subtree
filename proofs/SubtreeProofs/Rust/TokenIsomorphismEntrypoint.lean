module

public import SubtreeProofs.Rust.IndexedIsomorphismEntrypoint
public import SubtreeProofs.Rust.TokenMatchingEntrypoint
import Mathlib.Tactic

/-! # Total source correctness of the original-token isomorphism reference API -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.TokenIsomorphism

open OrderedSolver IndexedOrderedSolver TokenParser TokenMatching

/-- Actual parsing, structural optimum, original-index reconstruction and token
readback compose to the independent maximum isomorphism contract for both modes. -/
theorem maximum_common_token_isomorphism_spec (left right : Slice Bool) (rooted : Bool)
    (hl : Admissible left) (hr : Admissible right) :
    token_matching.maximum_common_token_isomorphism left right rooted ⦃ output => ∃ result,
      output = core.result.Result.Ok result ∧
      Paper2004.IndexedIso.MaximumTokens rooted left.val right.val
        (tokenView result.left) (tokenView result.right) result.edges.val ⦄ := by
  unfold token_matching.maximum_common_token_isomorphism
  apply WP.spec_bind (parse_balanced_tokens_spec left hl)
  rintro leftResult ⟨leftParsed,hLeftResult,hLeft⟩
  subst leftResult
  apply WP.spec_bind (parse_balanced_tokens_spec right hr)
  rintro rightResult ⟨rightParsed,hRightResult,hRight⟩
  subst rightResult
  obtain ⟨matching,hMatching,hCorrect⟩ := IndexedIsomorphism.maximum_common_isomorphism_indexed_spec
    leftParsed.word rightParsed.word rooted hLeft.pair_bound hRight.pair_bound
  simp only [hMatching,bind_ok]
  apply WP.spec_bind (emit_parsed_spec left leftParsed hLeft matching.left
    (Paper2004.IndexedIso.prunes_retains hCorrect.1))
  rintro leftOutput ⟨leftTokens,hLeftOutput,hLeftTokens⟩
  subst leftOutput
  apply WP.spec_bind (emit_parsed_spec right rightParsed hRight matching.right
    (Paper2004.IndexedIso.prunes_retains hCorrect.2.1))
  rintro rightOutput ⟨rightTokens,hRightOutput,hRightTokens⟩
  subst rightOutput
  simp only [WP.spec_ok]
  refine ⟨⟨leftTokens,rightTokens,matching.edges⟩,rfl,?_⟩
  simpa only [hLeft.encoded_input,hRight.encoded_input,hLeftTokens,hRightTokens] using
    Paper2004.IndexedIso.maximum_tokens rooted (toDyck leftParsed.word) (toDyck rightParsed.word)
      (model matching.left) (model matching.right) matching.edges.val hCorrect

def ResultSpec (left right : Slice Bool) (rooted : Bool)
    (output : core.result.Result token_matching.TokenCommonEmbedding token_matching.TokenMatchingError) : Prop :=
  match output with
  | .Ok result => Admissible left ∧ Admissible right ∧
      Paper2004.IndexedIso.MaximumTokens rooted left.val right.val
        (tokenView result.left) (tokenView result.right) result.edges.val
  | .Err (.LeftInput _) => ¬ Admissible left
  | .Err (.RightInput _) => Admissible left ∧ ¬ Admissible right
  | .Err _ => False

/-- Every represented call safely terminates with an independently maximum
original-token witness or the excluded input side, with left-input precedence.
Internal solver and original-index errors are unreachable on admitted inputs. -/
theorem maximum_common_token_isomorphism_total_spec (left right : Slice Bool) (rooted : Bool) :
    token_matching.maximum_common_token_isomorphism left right rooted ⦃ output => ResultSpec left right rooted output ⦄ := by
  classical
  by_cases hl : Admissible left
  · by_cases hr : Admissible right
    · apply WP.spec_mono (maximum_common_token_isomorphism_spec left right rooted hl hr)
      rintro output ⟨result,hOutput,hCorrect⟩
      subst output
      exact ⟨hl,hr,hCorrect⟩
    · unfold token_matching.maximum_common_token_isomorphism
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
  · unfold token_matching.maximum_common_token_isomorphism
    apply WP.spec_bind (parse_balanced_tokens_total_spec left)
    intro leftOutput hLeft
    cases leftOutput with
    | Err error =>
      simp only [WP.spec_ok,ResultSpec]
      exact hLeft
    | Ok parsed => exact False.elim (hl hLeft.1)

end SubtreeProofs.Rust.TokenIsomorphism

end
