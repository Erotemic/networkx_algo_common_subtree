import SubtreeProofs.Rust.SourceEvalCertificate

/-! Primitive and shared-reader fragments. These are not entire compiled
Rust mutants or a certificate for the actual evaluator's complete source. -/

namespace SourceEvalTests

open Lean SubtreeProofs.Rust
open LookupSource.Partial
open SourceEval

private def max32 : Nat := 2^32 - 1
example : checkedAdd32 max32 0 = some max32 := by decide +kernel
example : checkedAdd32 max32 1 = none := by decide +kernel
example : checkedAdd32 0 0 = some 0 := by decide +kernel
example : less32 max32 0 = some false := by decide +kernel
example : less32 (2^32) 0 = none := by decide +kernel

private def word : LookupSource.Value := .node .word 1 [.boxed (.node .word 0 []), .boxed (.node .word 0 [])]
private def state : State := fun slot =>
  if slot = 0 then .boolean true else if slot = 1 then Slot.ofValue word else .empty
private def noCalls : Calls := fun _ _ => none
private def view (result : Option (Outcome × Cost)) : Option (Bool × Nat × Nat × Nat) :=
  match result with
  | some (.returned (.boolean value), cost) => some (value, cost.work.steps, cost.destroyed.visits, cost.destroyed.boxes)
  | _ => none

-- A live word is destroyed explicitly and its two Boxes are counted.
example : view (exec noCalls (.step (.drop 1) .ret) state) = some (true, 7, 5, 2) := by decide +kernel
-- Shared referents are not recursively destroyed.
private def sharedState : State := state.set 1 (.shared word)
example : view (exec noCalls (.step (.drop 1) .ret) sharedState) = some (true, 3, 1, 0) := by decide +kernel
-- A repeated conditional drop adds only its statement step.
example : view (exec noCalls (.step (.drop 1) (.step (.drop 1) .ret)) state) = some (true, 8, 5, 2) := by decide +kernel
example : view (exec noCalls (.step .undefinedBehavior .ret) state) = none := by decide +kernel

-- Discriminants remain readable after payload movement; full parent read fails.
private def partialState : State := state.set 1 (.node .optional 1 [.empty])
private def branch : Code := .switch (.discriminant (.local 1)) [(.variant .optional 1, 0)] (some 1)
  .ret (.step .undefinedBehavior .done) .done
example : view (exec noCalls branch partialState) = some (true, 4, 0, 0) := by decide +kernel
example : (partialState.read (.local 1)).isNone = true := by decide +kernel

private def add : Code := .step (.call .checkedAdd [.number max32, .number 1] 0) .ret
private def addView : Option Bool :=
  match exec (run (fun _ => .done) 1) add (initialState []) with
  | some (.returned (.node .optional variant _), cost) => some (variant == 0 && cost.work.steps == 5)
  | _ => none
-- Numeric overflow returns None in the source value, not interpreter failure.
example : addView = some true := by decide +kernel
example : (Cost.entry .evaluate).solverCalls = 1 := rfl
example : (Cost.entry .checkedAdd).solverCalls = 0 := rfl

private def ctx : LookupSource.Frontend.Context := ⟨[(0, .tuple)], [], 4⟩
private def resolve (index : Nat) : LookupSource.Frontend.Read Function :=
  if index = 25 then .ok .checkedAdd else .error "unknown function"
private def drops (index : Nat) : Bool := index == 33
private def rejected (result : Except String α) : Bool := match result with | .error _ => true | .ok _ => false
private def numberType : Json := json% {"Untagged":{"Scalar":{"Integer":{"Unsigned":"U32"}}}}
private def literal (digits : String) : Json := json% {"Const":{"Untagged":[
  {"Integer":{"Unsigned":["U32",$(digits)]}},$(numberType)]}}

example : (Frontend.operand ctx 16 (literal "4294967295")).isOk = true := by decide +kernel
example : rejected (Frontend.operand ctx 16 (literal "4294967296")) = true := by decide +kernel
example : rejected (Frontend.operand ctx 16 (literal "-1")) = true := by decide +kernel
example : rejected (Frontend.expression ctx 16 (json% {"BinaryOp":["Add",$(literal "1"),$(literal "1")]})) = true := by decide +kernel
example : (Frontend.expression ctx 16 (json% {"BinaryOp":["Lt",$(literal "1"),$(literal "1")]})).isOk = true := by decide +kernel

private def readBody (statements : List Json) : Bool :=
  (Frontend.sequence resolve drops ctx 64 statements).isOk
example : readBody [json% {"kind":{"Borrowck":{"FakeRead":{"kind":{"Local":1}}}}},
    json% {"kind":"Return"}] = true := by decide +kernel
example : readBody [json% {"kind":{"Borrowck":{"Other":null}}},json% {"kind":"Return"}] = false := by decide +kernel
example : readBody [json% {"kind":"UndefinedBehavior"}] = true := by decide +kernel
example : readBody [json% {"kind":"UndefinedBehavior"},json% {"kind":"Return"}] = false := by decide +kernel
example : rejected (LookupSource.Frontend.unwind ctx
    (json% {"statements":[{"kind":"UnwindTerminate"}]})) = true := by decide +kernel
example : (LookupSource.Frontend.unwindWith true ctx
    (json% {"statements":[{"kind":"UnwindTerminate"}]})).isOk = true := by decide +kernel

private def dropJson (function : Nat) : Json := json% {
  "kind":"Conditional", "place":{"kind":{"Local":1}},
  "fn_ptr":{"kind":{"Fun":$(toJson function)}},"on_unwind":{"statements":[{"kind":"UnwindTerminate"}]}}
example : (Frontend.action resolve drops ctx 16 "Drop" (dropJson 33)).isOk = true := by decide +kernel
example : rejected (Frontend.action resolve drops ctx 16 "Drop" (dropJson 99)) = true := by decide +kernel

-- Behavioral checks of the actual decoded program. These native evaluations
-- are regressions; universal source/native and addressed refinements remain open.
private def emptyWord : LookupSource.Value := .node .word 0 []
private def pairWord : LookupSource.Value := .node .word 1 [.boxed emptyWord, .boxed emptyWord]
private def actual (fuel : Nat) (function : Function) (args : List LookupSource.Value) :=
  run Certificate.original.body fuel function args

private def wordScore : LookupSource.Value → Option Nat
  | .node .word 0 [] => some 0
  | .node .word 1 [.boxed (.node .word 0 []), .boxed (.node .word 0 [])] => some 1
  | _ => none

private def coreView (result : Option (LookupSource.Value × Cost)) : Option (Nat × Nat × Nat × Nat) :=
  match result with
  | some (.node .optional 1 [.node .embedding 0 [word, .number score]], cost) =>
    if wordScore word == some score then
      some (score, cost.work.events.allocations, cost.destroyed.boxes, cost.solverCalls)
    else none
  | _ => none

#guard coreView (actual 6 .maximum [.reference emptyWord, .reference emptyWord]) == some (0, 2, 2, 1)
#guard match coreView (actual 16 .maximum [.reference pairWord, .reference pairWord]) with
  | some (score, allocated, destroyed, calls) => score == 1 && allocated == destroyed + 2 && calls > 1
  | none => false

private def warm : LookupSource.Value := .node .table 1
  [.boxed (.node .entry 0 [emptyWord, emptyWord, .node .embedding 0 [emptyWord, .number max32]]),
   .boxed (.node .table 0 [])]
private def overflowView : Bool :=
  match actual 12 .evaluate [.reference pairWord, .reference pairWord, warm] with
  | some (.node .tuple 0 [.node .optional 0 [], .node .table 1
      [.boxed (.node .entry 0 [.node .word 0 [], .node .word 0 [],
        .node .embedding 0 [.node .word 0 [], .number cached]]), .boxed (.node .table 0 [])]], cost) =>
    cached == max32 && cost.solverCalls == 3 && cost.work.events.allocations == 0 && cost.destroyed.boxes == 0
  | _ => false
#guard overflowView

end SourceEvalTests
