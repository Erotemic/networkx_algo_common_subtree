module

public import SubtreeProofs.Rust.SourceResultOwnerProvenance
public import SubtreeProofs.Rust.SourceHeadFailureTotality

/-! A returned None has no witness owners, independently of the updated table's
old owners. Upgrade the constructed head-failure invocation without changing
its smaller-call contract or supplying a new physical execution premise. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem none_result_owners_above {world : World} {cell : Cell} {table : MemoTable} (bound : Nat)
    (readable : Readable world.memory world.live cell (encodeOutput none table)) :
    ResultOwnersAbove bound world.memory cell := by
  obtain ⟨used, graph, _⟩ := readable
  exact ResultOwnersAbove.of_zero graph (by simp [encodeOption, Slot.ofValue, ofFields, Slot.dropWork, dropFields])

theorem head_failure_total_fresh {world : World} {callers : List Activation} {previous : Resources} {guards : List Nat}
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
      ResultOwnersAbove world.memory.length final.memory packet.1 ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Recursive.original budget fuel world guards callers .evaluate
          (inputPackets leftCell rightCell tableCell (.Pair lh lt) (.Pair rh rt) table) = some (final, packet, cost) := by
  obtain ⟨fuel, budget, final, packet, cost, value, readable, wf, preserved, owned, evaluation, stable⟩ :=
    head_failure_total hw hc view lh lt rh rt table output leftCell rightCell tableCell leftRead rightRead tableRead
      input frame covered protectedReads miss childTotal headFailure
  have resultFresh : ResultOwnersAbove world.memory.length final.memory packet.1 :=
    none_result_owners_above _ (by rw [← value]; exact readable)
  exact ⟨fuel, budget, final, packet, cost, value, readable, wf, preserved, owned, evaluation, resultFresh, stable⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
