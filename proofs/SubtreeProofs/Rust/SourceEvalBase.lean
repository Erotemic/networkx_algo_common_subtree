module

public import SubtreeProofs.Rust.SourceEvalBody

/-! Base evaluator paths, with explicit callee executions and complete costs.
The actual source binding is composed in the source refinement module. -/

@[expose] public section

set_option maxRecDepth 8192
set_option maxHeartbeats 200000

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource LookupSource.Partial verified_ordered_core

attribute [local irreducible] recurseHeads recurseTails addScores addRoot contractLeft contractRight finish
  headsFailure tailsFailure subtotalOverflow rootOverflow leftFailure rightFailure cleanupLeft
  cleanupSubtotal cleanupTails cleanupHeads cleanupInputs leftPairCheck rightCases unreachable

def encodeOutput (result : Option CommonEmbedding) (table : MemoTable) : Value :=
  .node .tuple 0 [encodeOption result, encodeTable table]

def hitCost (lookupCost : Cost) : Cost :=
  ⟨⟨66 + lookupCost.work.steps, lookupCost.work.events⟩,
    lookupCost.destroyed.plus ⟨1, 0⟩, lookupCost.solverCalls⟩

theorem cache_hit_exec (call : Calls) (table : MemoTable) (left right : BalancedWord)
    (result : CommonEmbedding) (lookupCost : Cost)
    (hl : call .lookup [.reference (encodeTable table), .reference (encodeWord left), .reference (encodeWord right)] =
      some (encodeOption (some result), lookupCost)) :
    exec call body (initialState [.reference (encodeWord left), .reference (encodeWord right), encodeTable table]) =
      some (.returned (encodeOutput (some result) table), hitCost lookupCost) := by
  simp [body, start, cacheHit, returnResult, List.foldr_cons, List.foldr_nil,
    exec, Control.execWith, action, expression, operand, operands, scrutinee, returnValue, nextState,
    Control.selectSource, Control.selectIndex, initialState, Locals.lift, initialEnv, Locals.set,
    Locals.move, Locals.drop, Locals.read, splitPlace, Slot.take, Slot.get, Slot.read,
    Slot.materialize_ofValue, encodeOption, encodeResult, encodeOutput, Slot.ofValue, ofFields,
    Slot.materialize, materializeFields, Slot.dropWork, dropFields, hl,
    Cost.local, Cost.plus, hitCost, LookupSource.Cost.plus, LookupEvents.Events.plus, DropWork.plus,
    Action.weight, Expr.weight, Operand.weight, Place.weight, LookupSource.Scrutinee.weight,
    LookupSource.Operand.weight, bind, Option.bind, pure, Option.map]
  omega

def emptyWitness : CommonEmbedding := ⟨.Empty, 0#u32⟩

def missCost (localSteps : Nat) (lookupCost insertCost : Cost) : Cost :=
  ⟨⟨localSteps + lookupCost.work.steps + insertCost.work.steps,
      lookupCost.work.events.plus insertCost.work.events⟩,
    (lookupCost.destroyed.plus insertCost.destroyed).plus ⟨1, 0⟩,
    lookupCost.solverCalls + insertCost.solverCalls⟩

theorem empty_left_exec (call : Calls) (table : MemoTable) (right : BalancedWord)
    (output : MemoTable) (lookupCost insertCost : Cost)
    (hl : call .lookup [.reference (encodeTable table), .reference (encodeWord .Empty), .reference (encodeWord right)] =
      some (encodeOption none, lookupCost))
    (hi : call .insert [encodeTable table, .reference (encodeWord .Empty), .reference (encodeWord right),
      .reference (encodeResult emptyWitness)] = some (encodeTable output, insertCost)) :
    exec call body (initialState [.reference (encodeWord .Empty), .reference (encodeWord right), encodeTable table]) =
      some (.returned (encodeOutput (some emptyWitness) output), missCost 128 lookupCost insertCost) := by
  simp [encodeWord, encodeResult, emptyWitness] at hl hi
  simp only [↓reduceIte, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow, Nat.reduceEqDiff, Nat.reduceLT,
    Aeneas.Std.UScalar.ofNatCore_val_eq, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Option.map_eq_map, Key.variant.injEq, and_false, List.nil_append, List.cons_append, Option.all_none,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, Prod.mk.injEq, Cost.mk.injEq, LookupSource.Cost.mk.injEq,
    DropWork.mk.injEq, and_true, true_and, Nat.add_zero, Nat.zero_add,
    body, start, cacheMiss, emptyLeft, List.foldr_cons, List.foldr_nil,
    exec, Control.execWith, action, expression, operand, operands, scrutinee, returnValue, nextState,
    Control.selectSource, Control.selectIndex, initialState, Locals.lift, initialEnv, Locals.set,
    Locals.move, Locals.drop, Locals.read, splitPlace, Slot.take, Slot.get, Slot.read,
    Slot.materialize_ofValue, encodeOption, encodeResult, encodeOutput, encodeWord, emptyWitness,
    Slot.ofValue, ofFields, Slot.materialize, materializeFields, Slot.dropWork, dropFields, hl, hi,
    Cost.local, Cost.plus, missCost, LookupSource.Cost.plus, LookupEvents.Events.plus, DropWork.plus,
    Action.weight, Expr.weight, Operand.weight, Place.weight, LookupSource.Scrutinee.weight,
    LookupSource.Operand.weight, bind, Option.bind, pure, Option.map]
  omega

theorem empty_right_exec (call : Calls) (table : MemoTable) (head tail : BalancedWord)
    (output : MemoTable) (lookupCost insertCost : Cost)
    (hl : call .lookup [.reference (encodeTable table), .reference (encodeWord (.Pair head tail)), .reference (encodeWord .Empty)] =
      some (encodeOption none, lookupCost))
    (hi : call .insert [encodeTable table, .reference (encodeWord (.Pair head tail)), .reference (encodeWord .Empty),
      .reference (encodeResult emptyWitness)] = some (encodeTable output, insertCost)) :
    exec call body (initialState [.reference (encodeWord (.Pair head tail)), .reference (encodeWord .Empty), encodeTable table]) =
      some (.returned (encodeOutput (some emptyWitness) output), missCost 133 lookupCost insertCost) := by
  simp [encodeWord, encodeResult, emptyWitness] at hl hi
  simp only [↓reduceIte, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow, Nat.reduceEqDiff, Nat.reduceLT,
    Aeneas.Std.UScalar.ofNatCore_val_eq, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Option.map_eq_map, Key.variant.injEq, and_false, List.nil_append, List.cons_append, Option.all_none,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, Prod.mk.injEq, Cost.mk.injEq, LookupSource.Cost.mk.injEq,
    DropWork.mk.injEq, and_true, true_and, Nat.add_zero, Nat.zero_add,
    body, start, cacheMiss, rightCases, emptyRight, List.foldr_cons, List.foldr_nil,
    exec, Control.execWith, action, expression, operand, operands, scrutinee, returnValue, nextState,
    Control.selectSource, Control.selectIndex, initialState, Locals.lift, initialEnv, Locals.set,
    Locals.move, Locals.drop, Locals.read, splitPlace, Slot.take, Slot.get, Slot.read,
    Slot.materialize_ofValue, encodeOption, encodeResult, encodeOutput, encodeWord, emptyWitness,
    Slot.ofValue, ofFields, Slot.materialize, materializeFields, Slot.dropWork, dropFields, hl, hi,
    Cost.local, Cost.plus, missCost, LookupSource.Cost.plus, LookupEvents.Events.plus, DropWork.plus,
    Action.weight, Expr.weight, Operand.weight, Place.weight, LookupSource.Scrutinee.weight,
    LookupSource.Operand.weight, bind, Option.bind, pure, Option.map]
  omega

def baseSteps : BalancedWord → Nat
  | .Empty => 128
  | .Pair _ _ => 133

theorem empty_exec (call : Calls) (table : MemoTable) (left right : BalancedWord)
    (hempty : left = .Empty ∨ right = .Empty) (output : MemoTable) (lookupCost insertCost : Cost)
    (hl : call .lookup [.reference (encodeTable table), .reference (encodeWord left), .reference (encodeWord right)] =
      some (encodeOption none, lookupCost))
    (hi : call .insert [encodeTable table, .reference (encodeWord left), .reference (encodeWord right),
      .reference (encodeResult emptyWitness)] = some (encodeTable output, insertCost)) :
    exec call body (initialState [.reference (encodeWord left), .reference (encodeWord right), encodeTable table]) =
      some (.returned (encodeOutput (some emptyWitness) output), missCost (baseSteps left) lookupCost insertCost) := by
  cases left with
  | Empty => exact empty_left_exec call table right output lookupCost insertCost hl hi
  | Pair head tail =>
    rcases hempty with hbad | rfl
    · cases hbad
    · exact empty_right_exec call table head tail output lookupCost insertCost hl hi

end SubtreeProofs.Rust.SourceEval.Evaluator
