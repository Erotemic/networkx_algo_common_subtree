module

public import SubtreeProofs.Rust.TokenParserSpecification
import Mathlib.Tactic

/-!
# Actual parser safety and shape soundness on every represented input

The source recursion always advances before recursing. Every successful
segment has exactly its original Boolean encoding and consumed-token counter;
coordinate counts remain bounded and justify all subsequent mutations. These
properties apply to arbitrary token arrays, including malformed inputs.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.TokenParser

open OrderedSolver

structure SafeParsed (input : Slice Bool) (start : Usize) (initial : alloc.vec.Vec tokens.PairPositions)
    (result : tokens.ParsedForest) : Prop where
  next_eq : result.next.val = start.val+(wordTokens result.word).length
  next_bound : result.next.val ≤ input.length
  segment : input.val.drop start.val = wordTokens result.word ++ input.val.drop result.next.val
  positions_count : result.positions.length = initial.length+(toDyck result.word).semilength
  positions_bound : result.positions.length ≤ U32.max

def SafeOutcome (input : Slice Bool) (start : Usize) (positions : alloc.vec.Vec tokens.PairPositions)
    (output : core.result.Result tokens.ParsedForest tokens.TokenError) : Prop :=
  match output with
  | .Ok result => SafeParsed input start positions result
  | .Err _ => True

/-- No malformed token array can cause an out-of-bounds read, bad mutable
coordinate access, arithmetic failure or divergent parse. Successful segments
represent exactly the original consumed substring and a bounded pair count. -/
theorem parse_forest_total_spec (input : Slice Bool) (start : Usize) (positions : alloc.vec.Vec tokens.PairPositions)
    (hstart : start.val ≤ input.length) (hprevious : positions.length ≤ start.val) (hbudget : positions.length ≤ U32.max) :
    tokens.parse_forest input start positions ⦃ output => SafeOutcome input start positions output ⦄ := by
  have hlen := Slice.len_val input
  unfold tokens.parse_forest
  dsimp only
  split
  · rename_i he
    simp only [WP.spec_ok,SafeOutcome]
    refine ⟨?_,hstart,?_,?_,hbudget⟩
    · simp only [wordTokens_empty,List.length_nil,Nat.add_zero]
    · simp only [wordTokens_empty,List.nil_append]
    · simp only [toDyck,DyckWord.semilength_zero,Nat.add_zero]
  · rename_i hn
    have hi : start.val < input.length := by scalar_tac
    apply WP.spec_bind (Slice.index_usize_spec input start hi)
    intro bit hBit
    cases bit with
    | true =>
      simp only [↓reduceIte,WP.spec_ok,SafeOutcome]
      refine ⟨?_,hstart,?_,?_,hbudget⟩
      · simp only [wordTokens_empty,List.length_nil,Nat.add_zero]
      · simp only [wordTokens_empty,List.nil_append]
      · simp only [toDyck,DyckWord.semilength_zero,Nat.add_zero]
    | false =>
      simp only [Bool.false_eq_true,↓reduceIte]
      have hdropStart : input.val.drop start.val = false::input.val.drop (start.val+1) := by
        rw [List.drop_eq_getElem_cons hi,← hBit]
      apply WP.spec_bind (UScalar.cast_inBounds_spec .Usize core.num.U32.MAX u32_max_fits_usize)
      intro limit hLimit
      have hlimit : limit.val = U32.max := hLimit.trans u32_max_value
      have hpositionsLen := alloc.vec.Vec.len_val positions
      split
      · simp only [WP.spec_ok,SafeOutcome]
      · rename_i hnotLimit
        have hsmall : positions.length < U32.max := by scalar_tac
        apply WP.spec_bind (alloc.vec.Vec.push_spec positions (⟨start,start⟩ : tokens.PairPositions) (by scalar_tac))
        intro headPositions hPush
        have hpushLen : headPositions.length = positions.length+1 := by
          have he := congrArg List.length hPush
          simpa only [List.length_append,List.length_singleton] using he
        apply WP.spec_bind (Usize.add_spec (x := start) (y := 1#usize) (by scalar_tac))
        intro headStart hHeadStart
        have hheadStart : headStart.val = start.val+1 := by simpa using hHeadStart
        apply WP.spec_bind (parse_forest_total_spec input headStart headPositions (by omega) (by omega) (by omega))
        intro headOutput hHead
        cases headOutput with
        | Err error => simp only [WP.spec_ok,SafeOutcome]
        | Ok headResult =>
          dsimp only
          have hheadNext := hHead.next_eq
          have hheadBound := hHead.next_bound
          have hheadCount := hHead.positions_count
          have hheadBudget := hHead.positions_bound
          rw [wordTokens_length] at hheadNext
          split
          · simp only [WP.spec_ok,SafeOutcome]
          · rename_i hnotEnd
            have hc : headResult.next.val < input.length := by scalar_tac
            apply WP.spec_bind (Slice.index_usize_spec input headResult.next hc)
            intro bit hClosing
            cases bit with
            | false => simp only [Bool.false_eq_true,↓reduceIte,WP.spec_ok,SafeOutcome]
            | true =>
              simp only [↓reduceIte]
              have hdropClose : input.val.drop headResult.next.val = true::input.val.drop (headResult.next.val+1) := by
                rw [List.drop_eq_getElem_cons hc,← hClosing]
              have hindex : (alloc.vec.Vec.len positions).val < headResult.positions.length := by omega
              simp only [alloc.vec.Vec.index_mut_slice_index]
              apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec headResult.positions (alloc.vec.Vec.len positions) hindex)
              rintro ⟨record,back⟩ ⟨hRecord,hBack⟩
              apply WP.spec_bind (Usize.add_spec (x := headResult.next) (y := 1#usize) (by scalar_tac))
              intro tailStart hTailStart
              have htailStart : tailStart.val = headResult.next.val+1 := by simpa using hTailStart
              let updated := back { record with close := headResult.next }
              have hupdatedLen : updated.length = headResult.positions.length := by
                simp only [updated,hBack,alloc.vec.Vec.set_length]
              have hpreviousTail : updated.length ≤ tailStart.val := by omega
              apply WP.spec_bind (parse_forest_total_spec input tailStart updated (by omega) hpreviousTail (by omega))
              intro tailOutput hTail
              cases tailOutput with
              | Err error => simp only [WP.spec_ok,SafeOutcome]
              | Ok tailResult =>
                dsimp only
                have htailNext := hTail.next_eq
                have htailBound := hTail.next_bound
                have htailCount := hTail.positions_count
                have htailBudget := hTail.positions_bound
                rw [wordTokens_length] at htailNext
                simp only [WP.spec_ok,SafeOutcome]
                refine ⟨?_,htailBound,?_,?_,htailBudget⟩
                · simp only [wordTokens_length,toDyck,DyckWord.semilength_add,DyckWord.semilength_nest]
                  omega
                · rw [hdropStart,← hheadStart,hHead.segment,hdropClose,← htailStart,hTail.segment]
                  simp only [wordTokens_pair,List.cons_append,List.append_assoc]
                · simp only [toDyck,DyckWord.semilength_add,DyckWord.semilength_nest]
                  omega
termination_by input.length-start.val
decreasing_by all_goals omega

end SubtreeProofs.Rust.TokenParser

end
