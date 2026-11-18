module

public import SubtreeProofs.Rust.SourceEvaluatorCommonEntry

/-! The actual cache-hit branch and source-local transfer steps used to
construct it. The list split is definitionally the pinned branch; these helper
steps leave all physical execution and cost accounting in the existing engine. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def hitActions : List Action :=
  [.storageLive 9, .assign 9 (.use (.move (.field (.local 4) (some 1) 0))),
   .storageLive 10, .storageLive 11, .assign 11 (.use (.move (.local 9))),
   .assign 10 (.aggregate .optional 1 [.move (.local 11)]), .drop 11, .storageDead 11,
   .storageLive 12, .assign 12 (.use (.move (.local 3))),
   .assign 0 (.aggregate .tuple 0 [.move (.local 10), .move (.local 12)]),
   .drop 12, .storageDead 12, .drop 10, .storageDead 10, .drop 9, .storageDead 9,
   .drop 4, .storageDead 6, .storageDead 4]

def hitCode (index : Nat) : Code := (hitActions.drop index).foldr Control.Tree.step .done

theorem cacheHit_actions : cacheHit = hitActions.foldr Control.Tree.step .done := rfl

theorem move_local_source {state : State} {slot : Nat} {value : Value}
    (readable : (state slot).materialize = some value) :
    SourceEval.operand state (.move (.local slot)) = some (value, state.set slot .empty) := by
  simp only [SourceEval.operand, Partial.Locals.move, splitPlace, Slot.take, readable, bind, Option.bind]

theorem use_local_source {state : State} {slot : Nat} {value : Value}
    (readable : (state slot).materialize = some value) :
    SourceEval.expression state (.use (.move (.local slot))) = some (value, state.set slot .empty) :=
  move_local_source readable

theorem aggregate_one_source {state : State} {slot : Nat} {value : Value}
    (readable : (state slot).materialize = some value) (kind : Kind) (tag : Nat) :
    SourceEval.expression state (.aggregate kind tag [.move (.local slot)]) =
      some (.node kind tag [value], state.set slot .empty) := by
  simp only [SourceEval.expression, SourceEval.operands, move_local_source readable, bind, Option.bind]

theorem aggregate_two_source {state : State} {first second : Nat} {left right : Value}
    (firstReadable : (state first).materialize = some left) (secondReadable : (state second).materialize = some right)
    (different : second ≠ first) (kind : Kind) (tag : Nat) :
    SourceEval.expression state (.aggregate kind tag [.move (.local first), .move (.local second)]) =
      some (.node kind tag [left, right], (state.set first .empty).set second .empty) := by
  have secondRead : ((state.set first .empty) second).materialize = some right := by
    simpa only [Partial.Locals.set, different, ite_false] using secondReadable
  simp only [SourceEval.expression, SourceEval.operands, move_local_source firstReadable, move_local_source secondRead, bind, Option.bind]

theorem move_cached_payload_source {state : State} (result : CommonEmbedding)
    (initialized : state 4 = Slot.ofValue (encodeOption (some result))) :
    SourceEval.expression state (.use (.move (.field (.local 4) (some 1) 0))) =
      some (encodeResult result, state.set 4 (.node .optional 1 [.empty])) := by
  have node : state 4 = .node .optional 1 [Slot.ofValue (encodeResult result)] := by
    simpa only [encodeOption, Slot.ofValue, ofFields] using initialized
  simp [SourceEval.expression, SourceEval.operand, Partial.Locals.move, splitPlace, node, Slot.take,
    Slot.materialize_ofValue]

theorem cached_payload_hole_typed : SlotTyped (.node .optional 1 [.empty]) (.adt .optional) :=
  .node .some (.cons (.empty (.adt .embedding)) .nil)

end SubtreeProofs.Rust.SourceEval.Evaluator
