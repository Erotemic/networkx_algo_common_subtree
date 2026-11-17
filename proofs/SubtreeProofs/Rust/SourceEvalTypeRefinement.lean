module

public import SubtreeProofs.Rust.SourceEvalTypeCalls
public import SubtreeProofs.Rust.LookupBorrowOutputs
public import SubtreeProofs.Rust.SourceEvalTotal

/-! Actual recursive source typing, deep reference-free ordinary outputs and
composition with evaluator/native totality. Represented-output conclusions
require their explicit heap representation; this is not a whole addressed
execution, storage, owner or loan-lifetime theorem. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Types

open LookupSource Heap Partial

theorem output_closed (function : SourceEval.Function) (hf : function ≠ .boxNew) :
    Borrow.Closed (output function) := by
  cases function <;> first | contradiction | (repeat constructor)

theorem original_exec_typed (fuel : Nat) {locals : List Ty} {output : Ty} {state : State}
    {code : SourceEval.Code} {result : SourceEval.Outcome} {cost : SourceEval.Cost}
    (hs : LocalsTyped locals state) (hc : CodeConstraints locals output code)
    (hr : SourceEval.exec (run SourceEval.Certificate.original.body fuel) code state = some (result, cost)) :
    OutcomeTyped locals output result := exec_typed (original_run_typed fuel) hs hc hr

theorem original_result_typed (fuel : Nat) (function : SourceEval.Function) (hf : function ≠ .boxNew)
    {args : List Value} {value : Value} {cost : SourceEval.Cost}
    (hargs : SnapshotFieldsTyped args (inputs function))
    (hr : run SourceEval.Certificate.original.body fuel function args = some (value, cost)) :
    SnapshotTyped value (output function) := by
  apply original_run_typed fuel function args (inputs function) value cost (output function) hargs _ hr
  simp only [callOutput, hf, ite_false, SourceTypes.sameList_refl, ite_true]

theorem original_represented_output_unborrowed (fuel : Nat) (function : SourceEval.Function)
    (hf : function ≠ .boxNew) {args : List Value} {value : Value} {cost : SourceEval.Cost}
    (hargs : SnapshotFieldsTyped args (inputs function))
    (hr : run SourceEval.Certificate.original.body fuel function args = some (value, cost))
    {memory : Memory} {cell : Cell} (hrep : Represents memory cell value) : Borrow.Unborrowed memory cell :=
  Borrow.typed_unborrowed (hrep.typed (original_result_typed fuel function hf hargs hr)) (output_closed function hf)

theorem original_execute_typed (fuel : Nat) (function : SourceEval.Function) (hf : function ≠ .boxNew)
    {args : List Value} {value : Value} {cost : SourceEval.Cost}
    (hargs : SnapshotFieldsTyped args (inputs function))
    (hr : SourceEval.Certificate.executeSource Input.Program.source 512 fuel function args = .ok (some (value, cost))) :
    SnapshotTyped value (output function) := by
  rw [SourceEval.Certificate.original_execute] at hr
  exact original_result_typed fuel function hf hargs (Except.ok.inj hr)

end SubtreeProofs.Rust.SourceEval.Types

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap verified_ordered_core

theorem evaluate_typed {left right : BalancedWord} {table output : MemoTable}
    {fuel : Nat} {result : Option CommonEmbedding} {cost : SourceEval.Cost}
    (h : Evaluation fuel left right table result output cost) :
    SnapshotTyped (encodeOutput result output) (.tuple [.adt .optional, .adt .table]) :=
  Types.original_result_typed fuel .evaluate (by decide +kernel)
    (.cons (.shared (word_typed left)) (.cons (.shared (word_typed right)) (.cons (table_typed table) .nil))) h.source

theorem evaluate_total_typed (left right : BalancedWord) (table : MemoTable) :
    ∃ fuel result output cost, Evaluation fuel left right table result output cost ∧
      SnapshotTyped (encodeOutput result output) (.tuple [.adt .optional, .adt .table]) := by
  obtain ⟨fuel, result, output, cost, he⟩ := evaluate_total left right table
  exact ⟨fuel, result, output, cost, he, evaluate_typed he⟩

theorem evaluate_source_typed (left right : BalancedWord) (table : MemoTable) :
    ∃ fuel result output cost,
      Certificate.executeSource Input.Program.source 512 fuel .evaluate
        [.reference (encodeWord left), .reference (encodeWord right), encodeTable table] =
        .ok (some (encodeOutput result output, cost)) ∧
      memoized_common_embedding left right table = .ok (result, output) ∧
      SnapshotTyped (encodeOutput result output) (.tuple [.adt .optional, .adt .table]) := by
  obtain ⟨fuel, result, output, cost, he, ht⟩ := evaluate_total_typed left right table
  exact ⟨fuel, result, output, cost, by rw [Certificate.original_execute, he.source], he.native, ht⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
