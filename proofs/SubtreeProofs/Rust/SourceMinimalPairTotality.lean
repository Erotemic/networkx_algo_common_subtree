module

public import SubtreeProofs.Rust.SourceEvaluatorNativeFreshTotality

/-! The concrete one-edge-pair fresh contract is now an instance of universal
evaluator totality. Its existing statement and native empty-result helper remain
available to contraction-failure consumers. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem empty_request_some (left right : BalancedWord) (table : MemoTable)
    (empty : left = .Empty ∨ right = .Empty) :
    ∃ witness output, memoized_common_embedding left right table = .ok (some witness, output) := by
  cases found : MemoizedOrderedSolver.findResult table left right with
  | some result => exact ⟨result, table, cache_hit_native table left right result found⟩
  | none => exact ⟨emptyWitness, .Entry ⟨left, right, emptyWitness⟩ table, empty_native table left right empty found⟩

theorem native_minimal_pair_total_fresh : NativeTotalFresh (.Pair .Empty .Empty) (.Pair .Empty .Empty) :=
  native_total_fresh _ _

end SubtreeProofs.Rust.SourceEval.Evaluator
