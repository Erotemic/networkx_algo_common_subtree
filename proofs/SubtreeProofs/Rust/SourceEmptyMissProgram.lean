module

public import SubtreeProofs.Rust.SourceOriginalLoanMachine
public import SubtreeProofs.Rust.SourceCacheMissEntry
import Mathlib.Tactic.IntervalCases

/-! The pinned shared empty-query branch and its real suffixes. Native input
queries remain observed throughout witness construction and table transfer;
the copied tuple remains an unshared node throughout reference preparation. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def emptyActions : List Action :=
  [.storageLive 16, .storageLive 17, .assign 17 (.aggregate .word 0 []),
   .assign 16 (.aggregate .embedding 0 [.move (.local 17), .number 0]),
   .drop 17, .storageDead 17, .fakeRead (.local 16),
   .storageLive 18, .storageLive 19, .assign 19 (.use (.move (.local 3))),
   .storageLive 20, .assign 20 (.address (.deref (.local 1))),
   .storageLive 21, .assign 21 (.address (.deref (.local 2))),
   .storageLive 22, .storageLive 23, .assign 23 (.address (.local 16)),
   .assign 22 (.address (.deref (.local 23))),
   .call .insert [.move (.local 19), .move (.local 20), .move (.local 21), .move (.local 22)] 18,
   .storageDead 22, .storageDead 21, .storageDead 20, .storageDead 19, .fakeRead (.local 18), .storageDead 23,
   .storageLive 24, .storageLive 25, .assign 25 (.use (.move (.local 16))),
   .assign 24 (.aggregate .optional 1 [.move (.local 25)]), .drop 25, .storageDead 25,
   .storageLive 26, .assign 26 (.use (.move (.local 18))),
   .assign 0 (.aggregate .tuple 0 [.move (.local 24), .move (.local 26)]),
   .drop 26, .storageDead 26, .drop 24, .storageDead 24, .drop 18, .storageDead 18,
   .drop 16, .storageDead 16, .storageDead 13, .drop 3, .storageDead 3, .storageDead 2, .storageDead 1]

def emptyCode (index : Nat) : Code := (emptyActions.drop index).foldr Control.Tree.step .ret

theorem emptyLeft_actions : emptyLeft = emptyActions.foldr Control.Tree.step .ret := rfl

theorem empty_observes_queries (index : Nat) (bound : index ≤ 10) (slot : Nat) (member : slot ∈ [1, 2]) :
    LoanEnding.endsBeforeObservation slot (emptyCode index) = false := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> interval_cases index <;> decide +kernel

theorem InputLocals.prepare_empty {left right : BalancedWord} {table : MemoTable} {active : Activation}
    (h : InputLocals left right table active.state) (index : Nat) (bound : index ≤ 10) :
    InputLocals left right table (active.forgetRefs (emptyCode index)).state := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Activation.forgetRefs_observed active _ 1 (empty_observes_queries index bound 1 (by simp))]; exact h.left
  · rw [Activation.forgetRefs_observed active _ 2 (empty_observes_queries index bound 2 (by simp))]; exact h.right
  · exact (LoanEnding.forget_closed (emptyCode index) _ (by rw [h.table]; exact ofValue_typed (table_typed table)) (.adt .table)).trans h.table

theorem prepare_queryTuple {active : Activation} {left right : BalancedWord} (tuple : active.state 13 = queryTuple left right) (code : Code) :
    (active.forgetRefs code).state 13 = queryTuple left right := by
  exact (LoanEnding.forget_unshared code _ (by rw [tuple]; intro value same; cases same)).trans tuple

theorem MissScope.original_machine {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat} {left right : BalancedWord} {table : MemoTable}
    (scope : MissScope initial left right table world active) (h : LoanSafeMachine before callers previous external world active)
    (closed : ClosedOutside [1, 2, 13] active.state) (queries : QueryOrigins world active before.memory.length)
    (tupleOrigin : LoanOrigin world active before.memory.length 13) :
    OriginalLoanMachine before callers previous external [1, 2, 13] world active := by
  refine ⟨h, closed, ?_, ?_⟩
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · rw [scope.inputs.left]; simp only [Slot.dropWork]
    · rw [scope.inputs.right]; simp only [Slot.dropWork]
    · rw [scope.tuple]; simp [queryTuple, Slot.dropWork, dropFields, DropWork.plus]
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact queries 1 (by simp)
    · exact queries 2 (by simp)
    · exact tupleOrigin

theorem empty_word_source (state : State) :
    SourceEval.expression state (.aggregate .word 0 []) = some (encodeWord .Empty, state) := by
  simp only [SourceEval.expression, SourceEval.operands, bind, Option.bind, encodeWord]

theorem empty_result_source {state : State} (word : state 17 = Slot.ofValue (encodeWord .Empty)) :
    SourceEval.expression state (.aggregate .embedding 0 [.move (.local 17), .number 0]) =
      some (encodeResult emptyWitness, state.set 17 .empty) := by
  have moved := move_local_source (state := state) (slot := 17) (value := encodeWord .Empty)
    (by rw [word]; exact Slot.materialize_ofValue _)
  simp only [SourceEval.expression, SourceEval.operands, moved, bind, Option.bind]
  simp only [SourceEval.operand, show 0 < 2^32 by decide, ite_true]
  rfl

end SubtreeProofs.Rust.SourceEval.Evaluator
