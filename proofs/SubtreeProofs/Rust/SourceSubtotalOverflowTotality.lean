module

public import SubtreeProofs.Rust.SourceSubtotalOverflowBody
public import SubtreeProofs.Rust.SourceNoneResultProvenance

/-! Complete checked parent dispatch when both children succeed and their
subtotal overflows. The updated table survives both fresh witness drops. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core Aeneas.Std

theorem subtotal_overflow_native (table afterHeads output : MemoTable) (lh lt rh rt : BalancedWord) (heads tails : CommonEmbedding)
    (miss : MemoizedOrderedSolver.findResult table (.Pair lh lt) (.Pair rh rt) = none)
    (headSuccess : memoized_common_embedding lh rh table = .ok (some heads, afterHeads))
    (tailSuccess : memoized_common_embedding lt rt afterHeads = .ok (some tails, output))
    (overflow : Aeneas.Std.U32.checked_add heads.edges tails.edges = none) :
    memoized_common_embedding (.Pair lh lt) (.Pair rh rt) table = .ok (none, output) := by
  rw [memoized_common_embedding.eq_def, MemoizedOrderedSolver.memo_lookup_correct, miss, bind_ok]
  simp only [headSuccess, tailSuccess, overflow, lift, bind_ok, uncurry_apply_pair]

theorem subtotal_overflow_total_fresh {world : World} {callers : List Activation} {previous : Resources} {guards : List Nat}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (lh lt rh rt : BalancedWord) (table afterHeads output : MemoTable) (heads tails : CommonEmbedding)
    (leftCell rightCell tableCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord (.Pair lh lt))))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord (.Pair rh rt))))
    (tableRead : Readable world.memory world.live tableCell (encodeTable table))
    {owners external : List Nat}
    (input : FieldsFootprint world.memory [leftCell, rightCell, tableCell] owners)
    (frame : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external))) (protectedReads : guards ⊆ previous.reads)
    (miss : MemoizedOrderedSolver.findResult table (.Pair lh lt) (.Pair rh rt) = none)
    (headsTotal : NativeTotalFresh lh rh) (tailsTotal : NativeTotalFresh lt rt)
    (headSuccess : memoized_common_embedding lh rh table = .ok (some heads, afterHeads))
    (tailSuccess : memoized_common_embedding lt rt afterHeads = .ok (some tails, output))
    (overflow : Aeneas.Std.U32.checked_add heads.edges tails.edges = none) :
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
  obtain ⟨entered, active, fuel, budget, middle, after, cell, work, entryRun, machine, state, bodyRun, empty, separate, fresh, kept⟩ :=
    entry_subtotal_overflow_body_complete hw hc view lh lt rh rt table afterHeads output heads tails leftCell rightCell tableCell
      leftRead rightRead tableRead input frame covered miss headsTotal tailsTotal headSuccess tailSuccess overflow
  obtain ⟨final, packet, value, readable, wf, preserved, owned, evaluation, stable⟩ :=
    evaluator_body_close_total (.Pair lh lt) (.Pair rh rt) table leftCell rightCell tableCell fuel budget cell work none output
      entryRun machine state bodyRun empty separate fresh kept protectedReads
      (subtotal_overflow_native table afterHeads output lh lt rh rt heads tails miss headSuccess tailSuccess overflow)
  have resultFresh : ResultOwnersAbove world.memory.length final.memory packet.1 :=
    none_result_owners_above _ (by rw [← value]; exact readable)
  exact ⟨fuel + 1, budget, final, packet, _, value, readable, wf, preserved, owned, evaluation, resultFresh, stable⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
