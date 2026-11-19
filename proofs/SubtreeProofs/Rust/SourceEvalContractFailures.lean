module

public import SubtreeProofs.Rust.SourceEvalFailures

/-! Failures after candidate construction retain the last table and explicitly
account for candidate/query destruction, including fresh Boxes. Recursive-call
contracts are composed with actual source execution in the refinement module. -/

@[expose] public section

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource LookupSource.Partial verified_ordered_core

attribute [local irreducible] finish headsFailure tailsFailure subtotalOverflow rootOverflow rightFailure

def matched (heads tails : CommonEmbedding) (total : Aeneas.Std.U32) : CommonEmbedding :=
  ⟨.Pair heads.word tails.word, total⟩

theorem left_failure_exec (call : Calls) (table : MemoTable) (lh lt rh rt : BalancedWord)
    (heads tails : CommonEmbedding) (subtotal total : Aeneas.Std.U32) (contractedLeft : BalancedWord)
    (afterHeads afterTails output : MemoTable)
    (lookupCost headsCost tailsCost addCost rootCost boxHeadCost boxTailCost concatCost leftCost : Cost)
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
      some (encodeOutput none output, leftCost)) :
    exec call body (initialState [.reference (encodeWord (.Pair lh lt)), .reference (encodeWord (.Pair rh rt)), encodeTable table]) =
      some (.returned (encodeOutput none output),
        pathCost 373 (((Slot.ofValue (encodeResult (matched heads tails total))).dropWork.plus
          (Slot.ofValue (encodeWord contractedLeft)).dropWork).plus ⟨11, 0⟩)
          [lookupCost, headsCost, tailsCost, addCost, rootCost, boxHeadCost, boxTailCost, concatCost, leftCost]) := by
  have hheads : heads.edges.val < 2^32 := heads.edges.hmax
  have htails : tails.edges.val < 2^32 := tails.edges.hmax
  have hsubtotal : subtotal.val < 2^32 := subtotal.hmax
  have htotal : total.val < 2^32 := total.hmax
  norm_num at hheads htails hsubtotal htotal
  simp only [encodeWord, encodeOutput, encodeOption, encodeResult, encodeNumberOption] at hl hh ht ha hr hbh hbt hconcat hd
  simp only [↓reduceIte, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow, Nat.reduceEqDiff, Nat.reduceLT,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Option.map_eq_map, Key.variant.injEq, and_false, List.nil_append, List.cons_append, Option.all_none, Option.all_some, decide_true,
    List.set_cons_zero, List.set_cons_succ, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, Prod.mk.injEq, Cost.mk.injEq, LookupSource.Cost.mk.injEq,
    DropWork.mk.injEq, and_true, true_and, Nat.add_zero, Nat.zero_add,
    body, start, cacheMiss, rightCases, leftPairCheck, recurseHeads, recurseTails, addScores, addRoot, contractLeft, leftFailure, cleanupLeft, cleanupSubtotal, cleanupTails, cleanupHeads, cleanupInputs, returnResult, List.foldr_cons, List.foldr_nil,
    exec, Control.execWith, action, expression, operand, operands, scrutinee, returnValue, nextState,
    Control.selectSource, Control.selectIndex, initialState, Locals.lift, initialEnv, Locals.set,
    Locals.move, Locals.drop, Locals.read, splitPlace, Slot.take, Slot.get, Slot.read,
    Slot.materialize_ofValue, encodeOption, encodeResult, encodeOutput, matched, encodeWord,
    Slot.ofValue, ofFields, Slot.materialize, materializeFields, Slot.dropWork, dropFields, hl, hh, ht, ha, hr, hbh, hbt, hconcat, hd, hheads, htails, hsubtotal, htotal,
    Cost.local, Cost.plus, pathCost, LookupSource.Cost.plus, LookupEvents.Events.plus, DropWork.plus,
    Action.weight, Expr.weight, Operand.weight, Place.weight, LookupSource.Scrutinee.weight,
    LookupSource.Operand.weight, bind, Option.bind, pure, Option.map]
  omega

theorem right_failure_exec (call : Calls) (table : MemoTable) (lh lt rh rt : BalancedWord)
    (heads tails dropLeft : CommonEmbedding) (subtotal total : Aeneas.Std.U32) (contractedLeft contractedRight : BalancedWord)
    (afterHeads afterTails afterLeft output : MemoTable)
    (lookupCost headsCost tailsCost addCost rootCost boxHeadCost boxTailCost concatCost leftCost concatRightCost rightCost : Cost)
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
      some (encodeOutput none output, rightCost)) :
    exec call body (initialState [.reference (encodeWord (.Pair lh lt)), .reference (encodeWord (.Pair rh rt)), encodeTable table]) =
      some (.returned (encodeOutput none output),
        pathCost 449 (((((Slot.ofValue (encodeResult (matched heads tails total))).dropWork.plus
          (Slot.ofValue (encodeWord contractedLeft)).dropWork).plus (Slot.ofValue (encodeWord contractedRight)).dropWork).plus
          (Slot.ofValue (encodeResult dropLeft)).dropWork).plus ⟨13, 0⟩)
          [lookupCost, headsCost, tailsCost, addCost, rootCost, boxHeadCost, boxTailCost, concatCost, leftCost, concatRightCost, rightCost]) := by
  have hheads : heads.edges.val < 2^32 := heads.edges.hmax
  have htails : tails.edges.val < 2^32 := tails.edges.hmax
  have hsubtotal : subtotal.val < 2^32 := subtotal.hmax
  have htotal : total.val < 2^32 := total.hmax
  norm_num at hheads htails hsubtotal htotal
  simp only [encodeWord, encodeOutput, encodeOption, encodeResult, encodeNumberOption] at hl hh ht ha hr hbh hbt hconcat hd hconcatRight hdr
  simp (config := { maxSteps := 500000 }) only [↓reduceIte, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow, Nat.reduceEqDiff, Nat.reduceLT,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Option.map_eq_map, Key.variant.injEq, and_false, List.nil_append, List.cons_append, Option.all_none, Option.all_some, decide_true,
    List.set_cons_zero, List.set_cons_succ, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, Prod.mk.injEq, Cost.mk.injEq, LookupSource.Cost.mk.injEq,
    DropWork.mk.injEq, and_true, true_and, Nat.add_zero, Nat.zero_add,
    body, start, cacheMiss, rightCases, leftPairCheck, recurseHeads, recurseTails, addScores, addRoot, contractLeft, contractRight, rightFailure, cleanupLeft, cleanupSubtotal, cleanupTails, cleanupHeads, cleanupInputs, returnResult, List.foldr_cons, List.foldr_nil,
    exec, Control.execWith, action, expression, operand, operands, scrutinee, returnValue, nextState,
    Control.selectSource, Control.selectIndex, initialState, Locals.lift, initialEnv, Locals.set,
    Locals.move, Locals.drop, Locals.read, splitPlace, Slot.take, Slot.get, Slot.read,
    Slot.materialize_ofValue, encodeOption, encodeResult, encodeOutput, matched, encodeWord,
    Slot.ofValue, ofFields, Slot.materialize, materializeFields, Slot.dropWork, dropFields, hl, hh, ht, ha, hr, hbh, hbt, hconcat, hd, hconcatRight, hdr, hheads, htails, hsubtotal, htotal,
    Cost.local, Cost.plus, pathCost, LookupSource.Cost.plus, LookupEvents.Events.plus, DropWork.plus,
    Action.weight, Expr.weight, Operand.weight, Place.weight, LookupSource.Scrutinee.weight,
    LookupSource.Operand.weight, bind, Option.bind, pure, Option.map]
  omega

end SubtreeProofs.Rust.SourceEval.Evaluator
