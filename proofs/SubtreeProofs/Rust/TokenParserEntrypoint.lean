module

public import SubtreeProofs.Rust.TokenParserAccepted
public import SubtreeProofs.Rust.TokenParserTotal
import Mathlib.Tactic

/-! # Actual flat balanced-token public parser on independent admitted inputs -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.TokenParser

open OrderedSolver IndexedOrderedSolver Paper2004.TokenEncoding

/-- Independently balanced flat input within the exact source pair-count bound. -/
def Admissible (input : Slice Bool) : Prop :=
  ∃ word : DyckWord, input.val = encoded word ∧ word.semilength < 2^32

/-- Whole-input shape and exact original opening/closing coordinate records.
The independent original Dyck tree fixes each coordinate, not just its range. -/
structure CorrectParsed (input : Slice Bool) (result : tokens.ParsedForest) : Prop where
  encoded_input : input.val = encoded (toDyck result.word)
  next_end : result.next.val = input.length
  positions_exact : coordinateView result.positions = positionPairs (toDyck result.word).toTree 0
  pair_bound : (toDyck result.word).semilength < 2^32

/-- Every independently admitted balanced token array safely parses to exactly
its shape and original token coordinates. Local checks and index ranges are
derived by the recursive proof; no parsed tree/index table is a premise. -/
theorem parse_balanced_tokens_spec (input : Slice Bool) (ha : Admissible input) :
    tokens.parse_balanced_tokens input ⦃ output => ∃ result,
      output = core.result.Result.Ok result ∧ CorrectParsed input result ⦄ := by
  obtain ⟨word,hinput,hsmall⟩ := ha
  let desired := fromDyck word
  have htokens : wordTokens desired = input.val := by
    simpa only [wordTokens,desired,toDyck_fromDyck] using hinput.symm
  have hbudget : (alloc.vec.Vec.new tokens.PairPositions).length+(toDyck desired).semilength ≤ U32.max := by
    have hmax : U32.max = 2^32-1 := by rw [U32.max_eq]; norm_num
    have hn : word.semilength ≤ U32.max := by rw [hmax]; omega
    simpa only [alloc.vec.Vec.length,alloc.vec.Vec.new,alloc.vec.Vec.from_val,
      List.length_nil,Nat.zero_add,desired,toDyck_fromDyck] using hn
  have hwhole : input.val = [] ++ wordTokens desired ++ [] := by
    simpa only [List.nil_append,List.append_nil] using htokens.symm
  unfold tokens.parse_balanced_tokens
  apply WP.spec_bind (parse_forest_accepted_spec input desired 0#usize (alloc.vec.Vec.new tokens.PairPositions) [] []
    hwhole rfl (Or.inl rfl) hbudget (by simp))
  rintro output ⟨result,hOutput,hParsed⟩
  subst output
  have hnext := hParsed.next_eq
  have htokenLength : (wordTokens desired).length = input.length := by rw [htokens]
  have he : result.next = Slice.len input := by
    apply UScalar.eq_of_val_eq
    rw [Slice.len_val]
    simpa only [UScalar.ofNatCore_val_eq,Nat.zero_add,htokenLength] using hnext
  simp only [he,bne_self_eq_false,Bool.false_eq_true,↓reduceIte,WP.spec_ok]
  refine ⟨result,rfl,?_,?_,?_,?_⟩
  · rw [hParsed.word_eq]
    exact htokens.symm
  · exact (congrArg UScalar.val he).trans (Slice.len_val input)
  · have hp := hParsed.coordinates
    simpa only [coordinateView,alloc.vec.Vec.new,alloc.vec.Vec.from_val,
      List.map_nil,List.nil_append,UScalar.ofNatCore_val_eq,sourceShape_toTree,hParsed.word_eq] using hp
  · simpa only [hParsed.word_eq,desired,toDyck_fromDyck] using hsmall

/-- A returned source error is impossible for any independently admitted
input, including empty input and extreme allowed pair counts. -/
theorem parse_error_not_admissible (input : Slice Bool) (error : tokens.TokenError)
    (herror : tokens.parse_balanced_tokens input = .ok (.Err error)) : ¬ Admissible input := by
  intro ha
  have hs := parse_balanced_tokens_spec input ha
  rw [herror] at hs
  simp only [WP.spec_ok] at hs
  obtain ⟨result,he,_⟩ := hs
  cases he


/-- Coarse universally terminating wrapper contract used to rule out accepting
any malformed or oversized input, independently of coordinate reconstruction. -/
def ShapeResult (input : Slice Bool) (output : core.result.Result tokens.ParsedForest tokens.TokenError) : Prop :=
  match output with
  | .Ok result => input.val = wordTokens result.word ∧ (toDyck result.word).semilength < 2^32
  | .Err _ => True

theorem parse_balanced_tokens_shape_total_spec (input : Slice Bool) :
    tokens.parse_balanced_tokens input ⦃ output => ShapeResult input output ⦄ := by
  unfold tokens.parse_balanced_tokens
  apply WP.spec_bind (parse_forest_total_spec input 0#usize (alloc.vec.Vec.new tokens.PairPositions) (by simp) (by simp) (by simp))
  intro output hOutput
  cases output with
  | Err error => simp only [WP.spec_ok,ShapeResult]
  | Ok result =>
    dsimp only
    by_cases he : result.next = Slice.len input
    · simp only [he,bne_self_eq_false,Bool.false_eq_true,↓reduceIte,WP.spec_ok,ShapeResult]
      have hend : result.next.val = input.length := (congrArg UScalar.val he).trans (Slice.len_val input)
      have hsegment := hOutput.segment
      have hencoded : input.val = wordTokens result.word := by
        simpa only [UScalar.ofNatCore_val_eq,List.drop_zero,hend,Slice.length,List.drop_length,List.append_nil] using hsegment
      have hcount : result.positions.length = (toDyck result.word).semilength := by
        simpa only [alloc.vec.Vec.length,alloc.vec.Vec.new,alloc.vec.Vec.from_val,List.length_nil,Nat.zero_add] using hOutput.positions_count
      have hbound : (toDyck result.word).semilength ≤ U32.max := by
        rw [← hcount]
        exact hOutput.positions_bound
      have hmax : U32.max = 2^32-1 := by rw [U32.max_eq]; norm_num
      refine ⟨hencoded,?_⟩
      rw [hmax] at hbound
      omega
    · have hn : (result.next != Slice.len input) = true := bne_iff_ne.mpr he
      simp only [hn,↓reduceIte,WP.spec_ok,ShapeResult]

/-- Exact successful parsing or rejection of every independently excluded
flat input. The source error variants remain explicit; model failures and
divergence are ruled out on every represented input. -/
def ResultSpec (input : Slice Bool) (output : core.result.Result tokens.ParsedForest tokens.TokenError) : Prop :=
  match output with
  | .Ok result => Admissible input ∧ CorrectParsed input result
  | .Err _ => ¬ Admissible input

/-- Total correctness of the actual public flat-token parser on every input.
Success has exact original coordinates; rejection is exactly exclusion from
the independent balanced/u32-bounded domain. No parsed-result certificate is
an endpoint premise. -/
theorem parse_balanced_tokens_total_spec (input : Slice Bool) :
    tokens.parse_balanced_tokens input ⦃ output => ResultSpec input output ⦄ := by
  classical
  by_cases ha : Admissible input
  · apply WP.spec_mono (parse_balanced_tokens_spec input ha)
    rintro output ⟨result,hOutput,hCorrect⟩
    subst output
    exact ⟨ha,hCorrect⟩
  · apply WP.spec_mono (parse_balanced_tokens_shape_total_spec input)
    intro output hOutput
    cases output with
    | Err error => exact ha
    | Ok result => exact False.elim (ha ⟨toDyck result.word,hOutput.1,hOutput.2⟩)

end SubtreeProofs.Rust.TokenParser

end
