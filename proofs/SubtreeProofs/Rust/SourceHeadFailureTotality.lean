module

public import SubtreeProofs.Rust.SourceHeadFailureBody
public import SubtreeProofs.Rust.SourceEvaluatorBodyClosure

/-! Complete actual native evaluator invocation on the head-failure path.
The universal contract for the smaller head pair is explicit; an independent
native head failure selects the path. No successful physical parent run or
post-callee frame is supplied. Full pair/pair induction remains separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core Aeneas Aeneas.Std Result

theorem head_failure_native (table : MemoTable) (lh lt rh rt : BalancedWord) (output : MemoTable)
    (miss : MemoizedOrderedSolver.findResult table (.Pair lh lt) (.Pair rh rt) = none)
    (headFailure : memoized_common_embedding lh rh table = .ok (none, output)) :
    memoized_common_embedding (.Pair lh lt) (.Pair rh rt) table = .ok (none, output) := by
  rw [memoized_common_embedding.eq_def, MemoizedOrderedSolver.memo_lookup_correct, miss, bind_ok]
  simp only [headFailure, bind_ok, uncurry_apply_pair]

theorem head_failure_total {world : World} {callers : List Activation} {previous : Resources} {guards : List Nat}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (lh lt rh rt : BalancedWord) (table output : MemoTable) (leftCell rightCell tableCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord (.Pair lh lt))))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord (.Pair rh rt))))
    (tableRead : Readable world.memory world.live tableCell (encodeTable table))
    {owners external : List Nat}
    (input : FieldsFootprint world.memory [leftCell, rightCell, tableCell] owners)
    (frame : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external))) (protectedReads : guards ⊆ previous.reads)
    (miss : MemoizedOrderedSolver.findResult table (.Pair lh lt) (.Pair rh rt) = none)
    (childTotal : NativeTotal lh rh) (headFailure : memoized_common_embedding lh rh table = .ok (none, output)) :
    ∃ minimumFuel minimumBudget final packet cost,
      packet.2 = encodeOutput none output ∧ Readable final.memory final.live packet.1 packet.2 ∧
      final.WellFormed ∧ Preserves world final guards ∧
      (∃ outputOwners, Footprint final.memory packet.1 outputOwners ∧
        OwnerFrame final (outputOwners ++ (callerOwners final callers ++ external)) ∧
        BoxCoverage final (outputOwners ++ (callerOwners final callers ++ external))) ∧
      Evaluation minimumFuel (.Pair lh lt) (.Pair rh rt) table none output cost ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Recursive.original budget fuel world guards callers .evaluate
          (inputPackets leftCell rightCell tableCell (.Pair lh lt) (.Pair rh rt) table) = some (final, packet, cost) := by
  obtain ⟨entered, active, fuel, budget, middle, after, cell, work, entryRun, machine, state, bodyRun, empty, separate, fresh, kept⟩ :=
    entry_head_failure_body_complete hw hc view lh lt rh rt table output leftCell rightCell tableCell
      leftRead rightRead tableRead input frame covered miss childTotal headFailure
  obtain ⟨final, packet, value, readable, wf, preserved, owned, evaluation, stable⟩ :=
    evaluator_body_close_total (.Pair lh lt) (.Pair rh rt) table leftCell rightCell tableCell fuel budget cell work none output
      entryRun machine state bodyRun empty separate fresh kept protectedReads (head_failure_native table lh lt rh rt output miss headFailure)
  exact ⟨fuel + 1, budget, final, packet, _, value, readable, wf, preserved, owned, evaluation, stable⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
