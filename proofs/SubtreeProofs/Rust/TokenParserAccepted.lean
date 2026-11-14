module

public import SubtreeProofs.Rust.TokenParserSpecification
import Mathlib.Tactic

/-! # Actual checked recursive parsing of every admitted balanced segment -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.TokenParser

open OrderedSolver IndexedOrderedSolver Paper2004.TokenEncoding

/-- Actual source parsing safely consumes exactly an independently encoded
balanced forest, stopping at its closing token or at input end. Coordinate
records, counts and every checked range are derived from the original input. -/
theorem parse_forest_accepted_spec (input : Slice Bool) (word : BalancedWord) (start : Usize)
    (positions : alloc.vec.Vec tokens.PairPositions) (leading suffix : List Bool)
    (hinput : input.val = leading ++ wordTokens word ++ suffix) (hstart : start.val = leading.length)
    (hstop : Stops suffix) (hbudget : positions.length+(toDyck word).semilength ≤ U32.max)
    (hprevious : positions.length ≤ start.val) :
    tokens.parse_forest input start positions ⦃ output => ∃ result,
      output = core.result.Result.Ok result ∧ ParsedAs word start positions result ⦄ := by
  induction word generalizing start positions leading suffix with
  | Empty =>
    rcases hstop with rfl | ⟨rest,rfl⟩
    · have he : start = Slice.len input := by
        apply UScalar.eq_of_val_eq
        rw [Slice.len_val]
        simpa only [Slice.length,hinput,wordTokens_empty,List.append_nil] using hstart
      unfold tokens.parse_forest
      simp only [he,↓reduceIte,WP.spec_ok]
      refine ⟨⟨.Empty,Slice.len input,positions⟩,rfl,rfl,?_,?_⟩
      · simpa only [wordTokens_empty,List.length_nil,Nat.add_zero] using congrArg UScalar.val he.symm
      · simp only [sourceShape,positionPairs,List.append_nil]
    · have hlength : input.length = leading.length+1+rest.length := by
        simp only [Slice.length,hinput,wordTokens_empty,List.append_nil,List.length_append,List.length_cons]
        omega
      have hlen := Slice.len_val input
      have hn : start ≠ Slice.len input := by scalar_tac
      unfold tokens.parse_forest
      simp only [hn,↓reduceIte]
      apply WP.spec_bind (read_token_spec input start leading rest true (by simpa only [wordTokens_empty,List.append_nil] using hinput) hstart)
      intro bit hBit
      subst bit
      simp only [↓reduceIte,WP.spec_ok]
      refine ⟨⟨.Empty,start,positions⟩,rfl,rfl,?_,?_⟩
      · simp only [wordTokens_empty,List.length_nil,Nat.add_zero]
      · simp only [sourceShape,positionPairs,List.append_nil]
  | Pair head tail ihHead ihTail =>
    have hlen := Slice.len_val input
    have hlength : input.length = leading.length+(wordTokens head).length+(wordTokens tail).length+2+suffix.length := by
      simp only [Slice.length,hinput,wordTokens_pair,List.length_append,List.length_cons]
      omega
    have hpairBudget := hbudget
    simp only [toDyck,DyckWord.semilength_add,DyckWord.semilength_nest] at hpairBudget
    have hstartBound : start.val < input.length := by omega
    have hn : start ≠ Slice.len input := by scalar_tac
    have hfirst : input.val = leading ++ false::(wordTokens head ++ true::(wordTokens tail ++ suffix)) := by
      simpa only [wordTokens_pair,List.append_assoc,List.cons_append] using hinput
    unfold tokens.parse_forest
    simp only [hn,↓reduceIte]
    apply WP.spec_bind (read_token_spec input start leading (wordTokens head ++ true::(wordTokens tail ++ suffix)) false hfirst hstart)
    intro bit hBit
    subst bit
    simp only [Bool.false_eq_true,↓reduceIte]
    apply WP.spec_bind (UScalar.cast_inBounds_spec .Usize core.num.U32.MAX u32_max_fits_usize)
    intro limit hLimit
    have hlimit : limit.val = U32.max := hLimit.trans u32_max_value
    have hpositionsLen := alloc.vec.Vec.len_val positions
    have hnotLimit : alloc.vec.Vec.len positions ≠ limit := by scalar_tac
    simp only [hnotLimit,↓reduceIte]
    apply WP.spec_bind (position_push_spec positions ⟨start,start⟩ (by scalar_tac))
    intro headPositions hPush
    have hpushLen : headPositions.length = positions.length+1 := by
      have he := congrArg List.length hPush
      simpa only [coordinateView_length,List.length_append,List.length_singleton] using he
    apply WP.spec_bind (Usize.add_spec (x := start) (y := 1#usize) (by scalar_tac))
    intro headStart hHeadStart
    have hheadStart : headStart.val = start.val+1 := by simpa using hHeadStart
    have hheadInput : input.val = (leading++[false]) ++ wordTokens head ++ (true::(wordTokens tail++suffix)) := by
      simpa only [wordTokens_pair,List.append_assoc,List.cons_append,List.nil_append] using hinput
    have hheadIndex : headStart.val = (leading++[false]).length := by
      simp only [List.length_append,List.length_singleton]
      omega
    apply WP.spec_bind (ihHead headStart headPositions (leading++[false]) (true::(wordTokens tail++suffix))
      hheadInput hheadIndex (Or.inr ⟨wordTokens tail++suffix,rfl⟩) (by omega) (by omega))
    rintro headOutput ⟨headResult,hHeadOutput,hHead⟩
    subst headOutput
    have hheadNext := hHead.next_eq
    have hclose : headResult.next.val < input.length := by omega
    have hcloseValue : headResult.next.val = start.val+2*(toDyck head).semilength+1 := by
      rw [wordTokens_length] at hheadNext
      omega
    have hnotEnd : headResult.next ≠ Slice.len input := by scalar_tac
    simp only [hnotEnd,↓reduceIte]
    have hcloseInput : input.val = (leading++false::wordTokens head) ++ true::(wordTokens tail++suffix) := by
      simpa only [wordTokens_pair,List.append_assoc,List.cons_append] using hinput
    have hcloseIndex : headResult.next.val = (leading++false::wordTokens head).length := by
      simp only [List.length_append,List.length_cons]
      omega
    apply WP.spec_bind (read_token_spec input headResult.next (leading++false::wordTokens head) (wordTokens tail++suffix) true hcloseInput hcloseIndex)
    intro bit hBit
    subst bit
    simp only [↓reduceIte]
    have hrecordView : coordinateView headResult.positions = coordinateView positions ++
        (start.val,start.val)::positionPairs (sourceShape head) headStart.val := by
      rw [hHead.coordinates,hPush]
      simp only [positionValue,List.append_assoc,List.singleton_append]
    have hrecordIndex : (alloc.vec.Vec.len positions).val = (coordinateView positions).length := by
      rw [alloc.vec.Vec.len_val,coordinateView_length]
    apply WP.spec_bind (close_position_spec headResult.positions (alloc.vec.Vec.len positions) headResult.next
      (coordinateView positions) (positionPairs (sourceShape head) headStart.val) start.val start.val hrecordView hrecordIndex)
    rintro ⟨record,back⟩ ⟨hOpening,hClosed⟩
    apply WP.spec_bind (Usize.add_spec (x := headResult.next) (y := 1#usize) (by scalar_tac))
    intro tailStart hTailStart
    have htailStart : tailStart.val = headResult.next.val+1 := by simpa using hTailStart
    let updated := back { record with close := headResult.next }
    have hUpdated : coordinateView updated = coordinateView positions ++
        (start.val,headResult.next.val)::positionPairs (sourceShape head) headStart.val := hClosed
    have hupdatedLen : updated.length = positions.length+1+(toDyck head).semilength := by
      have he := congrArg List.length hUpdated
      simp only [coordinateView_length,List.length_append,List.length_cons,positionPairs_length,sourceShape_nodes] at he
      omega
    have htailInput : input.val = (leading++false::(wordTokens head++[true])) ++ wordTokens tail ++ suffix := by
      simpa only [wordTokens_pair,List.append_assoc,List.cons_append,List.nil_append] using hinput
    have htailIndex : tailStart.val = (leading++false::(wordTokens head++[true])).length := by
      simp only [List.length_append,List.length_cons,List.length_singleton,List.length_nil]
      omega
    have hpreviousTail : updated.length ≤ tailStart.val := by
      rw [wordTokens_length] at hheadNext
      omega
    apply WP.spec_bind (ihTail tailStart updated (leading++false::(wordTokens head++[true])) suffix
      htailInput htailIndex hstop (by omega) hpreviousTail)
    rintro tailOutput ⟨tailResult,hTailOutput,hTail⟩
    subst tailOutput
    simp only [WP.spec_ok]
    refine ⟨⟨.Pair headResult.word tailResult.word,tailResult.next,tailResult.positions⟩,rfl,?_,?_,?_⟩
    · simp only [hHead.word_eq,hTail.word_eq]
    · have ht := hTail.next_eq
      simp only [wordTokens_pair,List.length_cons,List.length_append]
      omega
    · rw [hTail.coordinates,hUpdated]
      simp only [sourceShape,positionPairs,sourceShape_nodes]
      rw [hheadStart,hcloseValue]
      have htailValue : tailStart.val = start.val+2*(toDyck head).semilength+2 := by omega
      rw [htailValue]
      simp only [List.append_assoc,List.cons_append]

end SubtreeProofs.Rust.TokenParser

end
