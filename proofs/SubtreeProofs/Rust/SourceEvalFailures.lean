module

public import SubtreeProofs.Rust.SourceEvalBase
public import SubtreeProofs.Rust.SourceEvalPathCost

/-! Recursive evaluator failure paths. Each rule retains the exact table
returned by its completed recursive callees and their full cost components.
Source/native recursive-call premises are discharged by later whole-run induction. -/

@[expose] public section

set_option maxRecDepth 16384
set_option maxHeartbeats 400000

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource LookupSource.Partial verified_ordered_core

attribute [local irreducible] recurseTails addScores addRoot contractLeft contractRight finish
  tailsFailure subtotalOverflow rootOverflow leftFailure rightFailure cleanupLeft
  cleanupSubtotal cleanupTails cleanupHeads unreachable

theorem heads_failure_exec (call : Calls) (table : MemoTable) (lh lt rh rt : BalancedWord)
    (output : MemoTable) (lookupCost headsCost : Cost)
    (hl : call .lookup [.reference (encodeTable table), .reference (encodeWord (.Pair lh lt)),
      .reference (encodeWord (.Pair rh rt))] = some (encodeOption none, lookupCost))
    (hh : call .evaluate [.reference (encodeWord lh), .reference (encodeWord rh), encodeTable table] =
      some (encodeOutput none output, headsCost)) :
    exec call body (initialState [.reference (encodeWord (.Pair lh lt)), .reference (encodeWord (.Pair rh rt)), encodeTable table]) =
      some (.returned (encodeOutput none output), pathCost 156 ⟨3, 0⟩ [lookupCost, headsCost]) := by
  simp only [encodeWord, encodeOutput, encodeOption] at hl hh
  simp only [↓reduceIte, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow, Nat.reduceEqDiff,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Option.map_eq_map, Key.variant.injEq, and_false, List.nil_append, List.cons_append, Option.all_none, Option.all_some, decide_true,
    List.set_cons_zero, List.set_cons_succ, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, Prod.mk.injEq, Cost.mk.injEq, LookupSource.Cost.mk.injEq,
    DropWork.mk.injEq, and_true, true_and, Nat.add_zero, Nat.zero_add,
    body, start, cacheMiss, rightCases, leftPairCheck, recurseHeads, headsFailure, cleanupInputs, returnResult, List.foldr_cons, List.foldr_nil,
    exec, Control.execWith, action, expression, operand, operands, scrutinee, returnValue, nextState,
    Control.selectSource, Control.selectIndex, initialState, Locals.lift, initialEnv, Locals.set,
    Locals.move, Locals.drop, Locals.read, splitPlace, Slot.take, Slot.get, Slot.read,
    Slot.materialize_ofValue, encodeOption, encodeOutput, encodeWord,
    Slot.ofValue, ofFields, Slot.materialize, materializeFields, Slot.dropWork, dropFields, hl, hh,
    Cost.local, Cost.plus, pathCost, LookupSource.Cost.plus, LookupEvents.Events.plus, DropWork.plus,
    Action.weight, Expr.weight, Operand.weight, Place.weight, LookupSource.Scrutinee.weight,
    LookupSource.Operand.weight, bind, Option.bind, pure, Option.map]
  omega


theorem tails_failure_exec (call : Calls) (table : MemoTable) (lh lt rh rt : BalancedWord)
    (heads : CommonEmbedding) (afterHeads output : MemoTable) (lookupCost headsCost tailsCost : Cost)
    (hl : call .lookup [.reference (encodeTable table), .reference (encodeWord (.Pair lh lt)),
      .reference (encodeWord (.Pair rh rt))] = some (encodeOption none, lookupCost))
    (hh : call .evaluate [.reference (encodeWord lh), .reference (encodeWord rh), encodeTable table] =
      some (encodeOutput (some heads) afterHeads, headsCost))
    (ht : call .evaluate [.reference (encodeWord lt), .reference (encodeWord rt), encodeTable afterHeads] =
      some (encodeOutput none output, tailsCost)) :
    exec call body (initialState [.reference (encodeWord (.Pair lh lt)), .reference (encodeWord (.Pair rh rt)), encodeTable table]) =
      some (.returned (encodeOutput none output),
        pathCost 208 ((Slot.ofValue (encodeResult heads)).dropWork.plus ⟨5, 0⟩) [lookupCost, headsCost, tailsCost]) := by
  simp only [encodeWord, encodeOutput, encodeOption, encodeResult] at hl hh ht
  simp only [↓reduceIte, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow, Nat.reduceEqDiff,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Option.map_eq_map, Key.variant.injEq, and_false, List.nil_append, List.cons_append, Option.all_none, Option.all_some, decide_true,
    List.set_cons_zero, List.set_cons_succ, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, Prod.mk.injEq, Cost.mk.injEq, LookupSource.Cost.mk.injEq,
    DropWork.mk.injEq, and_true, true_and, Nat.add_zero, Nat.zero_add,
    body, start, cacheMiss, rightCases, leftPairCheck, recurseHeads, recurseTails, tailsFailure, cleanupHeads, cleanupInputs, returnResult, List.foldr_cons, List.foldr_nil,
    exec, Control.execWith, action, expression, operand, operands, scrutinee, returnValue, nextState,
    Control.selectSource, Control.selectIndex, initialState, Locals.lift, initialEnv, Locals.set,
    Locals.move, Locals.drop, Locals.read, splitPlace, Slot.take, Slot.get, Slot.read,
    Slot.materialize_ofValue, encodeOption, encodeResult, encodeOutput, encodeWord,
    Slot.ofValue, ofFields, Slot.materialize, materializeFields, Slot.dropWork, dropFields, hl, hh, ht,
    Cost.local, Cost.plus, pathCost, LookupSource.Cost.plus, LookupEvents.Events.plus, DropWork.plus,
    Action.weight, Expr.weight, Operand.weight, Place.weight, LookupSource.Scrutinee.weight,
    LookupSource.Operand.weight, bind, Option.bind, pure, Option.map]
  omega


theorem subtotal_overflow_exec (call : Calls) (table : MemoTable) (lh lt rh rt : BalancedWord)
    (heads tails : CommonEmbedding) (afterHeads output : MemoTable) (lookupCost headsCost tailsCost addCost : Cost)
    (hl : call .lookup [.reference (encodeTable table), .reference (encodeWord (.Pair lh lt)),
      .reference (encodeWord (.Pair rh rt))] = some (encodeOption none, lookupCost))
    (hh : call .evaluate [.reference (encodeWord lh), .reference (encodeWord rh), encodeTable table] =
      some (encodeOutput (some heads) afterHeads, headsCost))
    (ht : call .evaluate [.reference (encodeWord lt), .reference (encodeWord rt), encodeTable afterHeads] =
      some (encodeOutput (some tails) output, tailsCost))
    (ha : call .checkedAdd [.number heads.edges.val, .number tails.edges.val] = some (encodeNumberOption none, addCost)) :
    exec call body (initialState [.reference (encodeWord (.Pair lh lt)), .reference (encodeWord (.Pair rh rt)), encodeTable table]) =
      some (.returned (encodeOutput none output),
        pathCost 238 (((Slot.ofValue (encodeResult heads)).dropWork.plus (Slot.ofValue (encodeResult tails)).dropWork).plus ⟨5, 0⟩)
          [lookupCost, headsCost, tailsCost, addCost]) := by
  have hheads : heads.edges.val < 2^32 := heads.edges.hmax
  have htails : tails.edges.val < 2^32 := tails.edges.hmax
  norm_num at hheads htails
  simp only [encodeWord, encodeOutput, encodeOption, encodeResult, encodeNumberOption] at hl hh ht ha
  simp only [↓reduceIte, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow, Nat.reduceEqDiff,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Option.map_eq_map, Key.variant.injEq, and_false, List.nil_append, List.cons_append, Option.all_none, Option.all_some, decide_true,
    List.set_cons_zero, List.set_cons_succ, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, Prod.mk.injEq, Cost.mk.injEq, LookupSource.Cost.mk.injEq,
    DropWork.mk.injEq, and_true, true_and, Nat.add_zero, Nat.zero_add,
    body, start, cacheMiss, rightCases, leftPairCheck, recurseHeads, recurseTails, addScores, subtotalOverflow, cleanupTails, cleanupHeads, cleanupInputs, returnResult, List.foldr_cons, List.foldr_nil,
    exec, Control.execWith, action, expression, operand, operands, scrutinee, returnValue, nextState,
    Control.selectSource, Control.selectIndex, initialState, Locals.lift, initialEnv, Locals.set,
    Locals.move, Locals.drop, Locals.read, splitPlace, Slot.take, Slot.get, Slot.read,
    Slot.materialize_ofValue, encodeOption, encodeResult, encodeOutput, encodeWord,
    Slot.ofValue, ofFields, Slot.materialize, materializeFields, Slot.dropWork, dropFields, hl, hh, ht, ha, hheads, htails,
    Cost.local, Cost.plus, pathCost, LookupSource.Cost.plus, LookupEvents.Events.plus, DropWork.plus,
    Action.weight, Expr.weight, Operand.weight, Place.weight, LookupSource.Scrutinee.weight,
    LookupSource.Operand.weight, bind, Option.bind, pure, Option.map]
  omega


theorem root_overflow_exec (call : Calls) (table : MemoTable) (lh lt rh rt : BalancedWord)
    (heads tails : CommonEmbedding) (subtotal : Aeneas.Std.U32) (afterHeads output : MemoTable) (lookupCost headsCost tailsCost addCost rootCost : Cost)
    (hl : call .lookup [.reference (encodeTable table), .reference (encodeWord (.Pair lh lt)),
      .reference (encodeWord (.Pair rh rt))] = some (encodeOption none, lookupCost))
    (hh : call .evaluate [.reference (encodeWord lh), .reference (encodeWord rh), encodeTable table] =
      some (encodeOutput (some heads) afterHeads, headsCost))
    (ht : call .evaluate [.reference (encodeWord lt), .reference (encodeWord rt), encodeTable afterHeads] =
      some (encodeOutput (some tails) output, tailsCost))
    (ha : call .checkedAdd [.number heads.edges.val, .number tails.edges.val] = some (encodeNumberOption (some subtotal.val), addCost))
    (hr : call .checkedAdd [.number subtotal.val, .number 1] = some (encodeNumberOption none, rootCost)) :
    exec call body (initialState [.reference (encodeWord (.Pair lh lt)), .reference (encodeWord (.Pair rh rt)), encodeTable table]) =
      some (.returned (encodeOutput none output),
        pathCost 260 (((Slot.ofValue (encodeResult heads)).dropWork.plus (Slot.ofValue (encodeResult tails)).dropWork).plus ⟨5, 0⟩)
          [lookupCost, headsCost, tailsCost, addCost, rootCost]) := by
  have hheads : heads.edges.val < 2^32 := heads.edges.hmax
  have htails : tails.edges.val < 2^32 := tails.edges.hmax
  have hsubtotal : subtotal.val < 2^32 := subtotal.hmax
  norm_num at hheads htails hsubtotal
  simp only [encodeWord, encodeOutput, encodeOption, encodeResult, encodeNumberOption] at hl hh ht ha hr
  simp only [↓reduceIte, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow, Nat.reduceEqDiff, Nat.reduceLT,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Option.map_eq_map, Key.variant.injEq, and_false, List.nil_append, List.cons_append, Option.all_none, Option.all_some, decide_true,
    List.set_cons_zero, List.set_cons_succ, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, Prod.mk.injEq, Cost.mk.injEq, LookupSource.Cost.mk.injEq,
    DropWork.mk.injEq, and_true, true_and, Nat.add_zero, Nat.zero_add,
    body, start, cacheMiss, rightCases, leftPairCheck, recurseHeads, recurseTails, addScores, addRoot, rootOverflow, cleanupSubtotal, cleanupTails, cleanupHeads, cleanupInputs, returnResult, List.foldr_cons, List.foldr_nil,
    exec, Control.execWith, action, expression, operand, operands, scrutinee, returnValue, nextState,
    Control.selectSource, Control.selectIndex, initialState, Locals.lift, initialEnv, Locals.set,
    Locals.move, Locals.drop, Locals.read, splitPlace, Slot.take, Slot.get, Slot.read,
    Slot.materialize_ofValue, encodeOption, encodeResult, encodeOutput, encodeWord,
    Slot.ofValue, ofFields, Slot.materialize, materializeFields, Slot.dropWork, dropFields, hl, hh, ht, ha, hr, hheads, htails, hsubtotal,
    Cost.local, Cost.plus, pathCost, LookupSource.Cost.plus, LookupEvents.Events.plus, DropWork.plus,
    Action.weight, Expr.weight, Operand.weight, Place.weight, LookupSource.Scrutinee.weight,
    LookupSource.Operand.weight, bind, Option.bind, pure, Option.map]
  omega

end SubtreeProofs.Rust.SourceEval.Evaluator
