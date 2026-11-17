module

public import SubtreeProofs.Rust.SourceEvalContractFailures

/-! Complete successful evaluator path, retaining every actual callee cost and
remaining local destruction. Callee contracts are discharged in the source/native
composition module; this is not an assumed whole-run resource envelope. -/

@[expose] public section

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource LookupSource.Partial verified_ordered_core

attribute [local irreducible] headsFailure tailsFailure subtotalOverflow rootOverflow leftFailure rightFailure

theorem success_exec (call : Calls) (table : MemoTable) (lh lt rh rt : BalancedWord)
    (heads tails dropLeft dropRight chosenFirst chosenFinal : CommonEmbedding) (subtotal total : Aeneas.Std.U32) (contractedLeft contractedRight : BalancedWord)
    (afterHeads afterTails afterLeft afterRight output : MemoTable)
    (lookupCost headsCost tailsCost addCost rootCost boxHeadCost boxTailCost concatCost leftCost concatRightCost rightCost choiceCost finalChoiceCost insertCost : Cost)
    (hl : call .lookup [.reference (encodeTable table), .reference (encodeWord (.Pair lh lt)),
      .reference (encodeWord (.Pair rh rt))] = some (encodeOption none, lookupCost))
    (hh : call .evaluate [.reference (encodeWord lh), .reference (encodeWord rh), encodeTable table] =
      some (encodeOutput (some heads) afterHeads, headsCost))
    (ht : call .evaluate [.reference (encodeWord lt), .reference (encodeWord rt), encodeTable afterHeads] =
      some (encodeOutput (some tails) afterTails, tailsCost))
    (ha : call .checkedAdd [.number heads.edges.val, .number tails.edges.val] =
      some (encodeNumberOption (some subtotal.val), addCost))
    (hr : call .checkedAdd [.number subtotal.val, .number 1] = some (encodeNumberOption (some total.val), rootCost))
    (hbh : call .boxNew [encodeWord heads.word] = some (.boxed (encodeWord heads.word), boxHeadCost))
    (hbt : call .boxNew [encodeWord tails.word] = some (.boxed (encodeWord tails.word), boxTailCost))
    (hconcat : call .concatenate [.reference (encodeWord lh), .reference (encodeWord lt)] = some (encodeWord contractedLeft, concatCost))
    (hd : call .evaluate [.reference (encodeWord contractedLeft), .reference (encodeWord (.Pair rh rt)), encodeTable afterTails] =
      some (encodeOutput (some dropLeft) afterLeft, leftCost))
    (hconcatRight : call .concatenate [.reference (encodeWord rh), .reference (encodeWord rt)] =
      some (encodeWord contractedRight, concatRightCost))
    (hdr : call .evaluate [.reference (encodeWord (.Pair lh lt)), .reference (encodeWord contractedRight), encodeTable afterLeft] =
      some (encodeOutput (some dropRight) afterRight, rightCost))
    (hchoice : call .chooseLonger [encodeResult (matched heads tails total), encodeResult dropLeft] =
      some (encodeResult chosenFirst, choiceCost))
    (hfinal : call .chooseLonger [encodeResult chosenFirst, encodeResult dropRight] = some (encodeResult chosenFinal, finalChoiceCost))
    (hi : call .insert [encodeTable afterRight, .reference (encodeWord (.Pair lh lt)), .reference (encodeWord (.Pair rh rt)),
      .reference (encodeResult chosenFinal)] = some (encodeTable output, insertCost)) :
    exec call body (initialState [.reference (encodeWord (.Pair lh lt)), .reference (encodeWord (.Pair rh rt)), encodeTable table]) =
      some (.returned (encodeOutput (some chosenFinal) output),
        pathCost 525 (((Slot.ofValue (encodeWord contractedLeft)).dropWork.plus
          (Slot.ofValue (encodeWord contractedRight)).dropWork).plus ⟨13, 0⟩)
          [lookupCost, headsCost, tailsCost, addCost, rootCost, boxHeadCost, boxTailCost,
            concatCost, leftCost, concatRightCost, rightCost, choiceCost, finalChoiceCost, insertCost]) := by
  have hheads : heads.edges.val < 2^32 := heads.edges.hmax
  have htails : tails.edges.val < 2^32 := tails.edges.hmax
  have hsubtotal : subtotal.val < 2^32 := subtotal.hmax
  have htotal : total.val < 2^32 := total.hmax
  norm_num at hheads htails hsubtotal htotal
  simp only [encodeWord, encodeOutput, encodeOption, encodeResult, encodeNumberOption, matched] at hl hh ht ha hr hbh hbt hconcat hd hconcatRight hdr hchoice hfinal hi
  simp (config := { maxSteps := 1000000 }) only [↓reduceIte, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow, Nat.reduceEqDiff, Nat.reduceLT,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Option.map_eq_map, Key.variant.injEq, and_false, List.nil_append, List.cons_append, Option.all_none, Option.all_some, decide_true,
    List.set_cons_zero, List.set_cons_succ, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, Prod.mk.injEq, Cost.mk.injEq, LookupSource.Cost.mk.injEq,
    DropWork.mk.injEq, and_true, true_and, Nat.add_zero, Nat.zero_add,
    body, start, cacheMiss, rightCases, leftPairCheck, recurseHeads, recurseTails, addScores, addRoot, contractLeft, contractRight, finish, cleanupLeft, cleanupSubtotal, cleanupTails, cleanupHeads, cleanupInputs, returnResult, List.foldr_cons, List.foldr_nil,
    exec, Control.execWith, action, expression, operand, operands, scrutinee, returnValue, nextState,
    Control.selectSource, Control.selectIndex, initialState, Locals.lift, initialEnv, Locals.set,
    Locals.move, Locals.drop, Locals.read, splitPlace, Slot.take, Slot.get, Slot.read,
    Slot.materialize_ofValue, encodeOption, encodeResult, encodeOutput, encodeWord,
    Slot.ofValue, ofFields, Slot.materialize, materializeFields, Slot.dropWork, dropFields, hl, hh, ht, ha, hr, hbh, hbt, hconcat, hd, hconcatRight, hdr, hchoice, hfinal, hi, hheads, htails, hsubtotal, htotal,
    Cost.local, Cost.plus, pathCost, LookupSource.Cost.plus, LookupEvents.Events.plus, DropWork.plus,
    Action.weight, Expr.weight, Operand.weight, Place.weight, LookupSource.Scrutinee.weight,
    LookupSource.Operand.weight, bind, Option.bind, pure, Option.map]
  omega

end SubtreeProofs.Rust.SourceEval.Evaluator
