import SubtreeProofs.Rust.SourceEvalTypeRefinement

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource SubtreeProofs.Rust.LookupSource.Heap
open SubtreeProofs.Rust.LookupSource.Partial verified_ordered_core

-- Recursive discharge has no typed-callee premise left and applies at every
-- fuel, including polymorphic Box instances.
example (fuel : Nat) : SourceEval.Types.CallsTyped (SourceEval.run SourceEval.Certificate.original.body fuel) :=
  SourceEval.Types.original_run_typed fuel

example (left right : BalancedWord) (table : MemoTable) :
    ∃ fuel result output cost,
      SourceEval.Certificate.executeSource SourceEval.Input.Program.source 512 fuel .evaluate
        [.reference (encodeWord left), .reference (encodeWord right), encodeTable table] =
        .ok (some (SourceEval.Evaluator.encodeOutput result output, cost)) ∧
      memoized_common_embedding left right table = .ok (result, output) ∧
      SnapshotTyped (SourceEval.Evaluator.encodeOutput result output) (.tuple [.adt .optional, .adt .table]) :=
  SourceEval.Evaluator.evaluate_source_typed left right table

-- The same type proof covers every actual overflow/failure result and its
-- complete cost, independently of cache soundness or witness/score agreement.
example (left right : BalancedWord) (table output : MemoTable) (fuel : Nat) (cost : SourceEval.Cost)
    (h : SourceEval.Evaluator.Evaluation fuel left right table none output cost) :
    SnapshotTyped (SourceEval.Evaluator.encodeOutput none output) (.tuple [.adt .optional, .adt .table]) :=
  SourceEval.Evaluator.evaluate_typed h

example : SnapshotTyped (SourceEval.encodeNumberOption (SourceEval.checkedAdd32 4294967295 1)) (.option .u32) :=
  SourceEval.Types.checkedAdd32_typed _ _

-- Ordinary outputs are deeply closed, including the evaluator's option/table
-- tuple. Polymorphic Box can contain a shared reference and is excluded.
example : Borrow.Closed (SourceEval.Types.output .evaluate) :=
  SourceEval.Types.output_closed .evaluate (by decide +kernel)
example : ¬ Borrow.Closed (.owned (.shared (.adt .word))) := by
  intro h
  cases h with | owned h => cases h

example : SnapshotTyped (.boxed (.reference (.node .word 0 []))) (.owned (.shared (.adt .word))) := by
  apply SourceEval.Types.original_run_typed 1 .boxNew [.reference (.node .word 0 [])]
    [.shared (.adt .word)] _ (SourceEval.Cost.entry .boxNew) _
  · exact .cons (.shared (.node .emptyWord .nil)) .nil
  · simp [SourceEval.Types.callOutput]
  · rfl

-- Preservation alone does not imply that arbitrary well-typed bodies return.
private def stopped : SourceEval.Function → SourceEval.Code := fun _ => .done
private theorem stopped_typed : SourceEval.Types.BodiesTyped stopped := by
  intro function _ _
  refine ⟨SourceEval.Types.output function :: SourceEval.Types.inputs function, ?_, .done⟩
  change List.take (List.length (SourceEval.Types.output function :: SourceEval.Types.inputs function)) _ = _
  exact List.take_length

example : SourceEval.Types.CallsTyped (SourceEval.run stopped 1) :=
  SourceEval.Types.run_typed stopped stopped_typed 1
example : SourceEval.run stopped 1 .evaluate [] = none := rfl
