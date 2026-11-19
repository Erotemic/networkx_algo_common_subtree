module

public import SubtreeProofs.Rust.SourceRightFailureBody
public import SubtreeProofs.Rust.SourceNoneResultProvenance

/-! Complete checked parent dispatch on right-contraction None. The updated
table survives both query drops, left-witness/candidate cleanup and all joins. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core Aeneas.Std

theorem right_failure_native (table afterHeads afterTails afterLeft output : MemoTable) (lh lt rh rt : BalancedWord) (heads tails leftWitness : CommonEmbedding) (subtotal total : Aeneas.Std.U32)
    (miss : MemoizedOrderedSolver.findResult table (.Pair lh lt) (.Pair rh rt) = none)
    (headSuccess : memoized_common_embedding lh rh table = .ok (some heads, afterHeads))
    (tailSuccess : memoized_common_embedding lt rt afterHeads = .ok (some tails, afterTails))
    (subtotalSuccess : Aeneas.Std.U32.checked_add heads.edges tails.edges = some subtotal)
    (rootSuccess : Aeneas.Std.U32.checked_add subtotal 1#u32 = some total)
    (leftSuccess : memoized_common_embedding (OrderedSolver.appendWord lh lt) (.Pair rh rt) afterTails = .ok (some leftWitness, afterLeft))
    (rightFailure : memoized_common_embedding (.Pair lh lt) (OrderedSolver.appendWord rh rt) afterLeft = .ok (none, output)) :
    memoized_common_embedding (.Pair lh lt) (.Pair rh rt) table = .ok (none, output) := by
  rw [memoized_common_embedding.eq_def, MemoizedOrderedSolver.memo_lookup_correct, miss, bind_ok]
  simp only [headSuccess, tailSuccess, subtotalSuccess, rootSuccess, lift, bind_ok, uncurry_apply_pair, OrderedSolver.concatenate_correct, leftSuccess, rightFailure]

theorem right_failure_total_fresh {world : World} {callers : List Activation} {previous : Resources} {guards : List Nat}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (lh lt rh rt : BalancedWord) (table afterHeads afterTails output : MemoTable) (heads tails : CommonEmbedding)
    (subtotal total : Aeneas.Std.U32) (leftCell rightCell tableCell : Cell)
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
    (tailSuccess : memoized_common_embedding lt rt afterHeads = .ok (some tails, afterTails))
    (subtotalSuccess : Aeneas.Std.U32.checked_add heads.edges tails.edges = some subtotal)
    (rootSuccess : Aeneas.Std.U32.checked_add subtotal 1#u32 = some total)
    (leftTotal : NativeTotalFresh (OrderedSolver.appendWord lh lt) (.Pair rh rt))
    (leftWitness : CommonEmbedding) (afterLeft : MemoTable)
    (leftSuccess : memoized_common_embedding (OrderedSolver.appendWord lh lt) (.Pair rh rt) afterTails = .ok (some leftWitness, afterLeft))
    (rightTotal : NativeTotalFresh (.Pair lh lt) (OrderedSolver.appendWord rh rt))
    (rightFailure : memoized_common_embedding (.Pair lh lt) (OrderedSolver.appendWord rh rt) afterLeft = .ok (none, output)) :
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
    entry_right_failure_body_complete hw hc view lh lt rh rt table afterHeads afterTails output heads tails subtotal total leftCell rightCell tableCell
      leftRead rightRead tableRead input frame covered miss headsTotal tailsTotal headSuccess tailSuccess subtotalSuccess rootSuccess leftTotal leftWitness afterLeft leftSuccess rightTotal rightFailure
  obtain ⟨final, packet, value, readable, wf, preserved, owned, evaluation, stable⟩ :=
    evaluator_body_close_total (.Pair lh lt) (.Pair rh rt) table leftCell rightCell tableCell fuel budget cell work none output
      entryRun machine state bodyRun empty separate fresh kept protectedReads
      (right_failure_native table afterHeads afterTails afterLeft output lh lt rh rt heads tails leftWitness subtotal total miss headSuccess tailSuccess subtotalSuccess rootSuccess leftSuccess rightFailure)
  have resultFresh : ResultOwnersAbove world.memory.length final.memory packet.1 :=
    none_result_owners_above _ (by rw [← value]; exact readable)
  exact ⟨fuel + 1, budget, final, packet, _, value, readable, wf, preserved, owned, evaluation, resultFresh, stable⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
