module

public import SubtreeProofs.Rust.SourcePairSuccessfulBody
public import SubtreeProofs.Rust.SourceEvaluatorBodyFreshClosure

/-! Actual successful pair/pair dispatch with complete ownership, native/source
agreement and witness-field provenance from four smaller fresh contracts. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core Aeneas.Std

theorem pair_successful_native (lh lt rh rt : BalancedWord) (table afterHeads afterTails afterLeft afterRight : MemoTable)
    (heads tails left right : CommonEmbedding) (subtotal total : Aeneas.Std.U32)
    (miss : MemoizedOrderedSolver.findResult table (.Pair lh lt) (.Pair rh rt) = none)
    (headSuccess : memoized_common_embedding lh rh table = .ok (some heads, afterHeads))
    (tailSuccess : memoized_common_embedding lt rt afterHeads = .ok (some tails, afterTails))
    (subtotalSuccess : Aeneas.Std.U32.checked_add heads.edges tails.edges = some subtotal)
    (rootSuccess : Aeneas.Std.U32.checked_add subtotal 1#u32 = some total)
    (leftSuccess : memoized_common_embedding (OrderedSolver.appendWord lh lt) (.Pair rh rt) afterTails = .ok (some left, afterLeft))
    (rightSuccess : memoized_common_embedding (.Pair lh lt) (OrderedSolver.appendWord rh rt) afterLeft = .ok (some right, afterRight)) :
    let result := selectedWitness (matchedWitness heads tails total) left right
    memoized_common_embedding (.Pair lh lt) (.Pair rh rt) table =
      .ok (some result, .Entry ⟨.Pair lh lt, .Pair rh rt, result⟩ afterRight) := by
  dsimp only
  rw [memoized_common_embedding.eq_def, MemoizedOrderedSolver.memo_lookup_correct, miss, bind_ok]
  simp only [headSuccess, tailSuccess, bind_ok, uncurry_apply_pair, lift, subtotalSuccess, rootSuccess,
    OrderedSolver.concatenate_correct, leftSuccess, rightSuccess, OrderedSolver.choose_longer_correct,
    MemoizedOrderedSolver.memo_insert_correct, selectedWitness, matchedWitness]

theorem pair_successful_total_fresh {world : World} {callers : List Activation} {previous : Resources} {guards : List Nat}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (lh lt rh rt : BalancedWord) (table afterHeads afterTails : MemoTable) (heads tails : CommonEmbedding)
    (subtotal total : Aeneas.Std.U32) (leftCell rightCell tableCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord (.Pair lh lt))))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord (.Pair rh rt))))
    (tableRead : Readable world.memory world.live tableCell (encodeTable table))
    {owners external : List Nat}
    (input : FieldsFootprint world.memory [leftCell, rightCell, tableCell] owners)
    (frame : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (protectedReads : guards ⊆ previous.reads)
    (miss : MemoizedOrderedSolver.findResult table (.Pair lh lt) (.Pair rh rt) = none)
    (headsTotal : NativeTotalFresh lh rh) (tailsTotal : NativeTotalFresh lt rt)
    (headSuccess : memoized_common_embedding lh rh table = .ok (some heads, afterHeads))
    (tailSuccess : memoized_common_embedding lt rt afterHeads = .ok (some tails, afterTails))
    (subtotalSuccess : Aeneas.Std.U32.checked_add heads.edges tails.edges = some subtotal)
    (rootSuccess : Aeneas.Std.U32.checked_add subtotal 1#u32 = some total)
    (leftTotal : NativeTotalFresh (OrderedSolver.appendWord lh lt) (.Pair rh rt))
    (left : CommonEmbedding) (afterLeft : MemoTable)
    (leftSuccess : memoized_common_embedding (OrderedSolver.appendWord lh lt) (.Pair rh rt) afterTails = .ok (some left, afterLeft))
    (rightTotal : NativeTotalFresh (.Pair lh lt) (OrderedSolver.appendWord rh rt))
    (right : CommonEmbedding) (afterRight : MemoTable)
    (rightSuccess : memoized_common_embedding (.Pair lh lt) (OrderedSolver.appendWord rh rt) afterLeft = .ok (some right, afterRight)) :
    let result := selectedWitness (matchedWitness heads tails total) left right
    let output := MemoTable.Entry ⟨.Pair lh lt, .Pair rh rt, result⟩ afterRight
    ∃ minimumFuel minimumBudget final packet cost,
      packet.2 = encodeOutput (some result) output ∧
      memoized_common_embedding (.Pair lh lt) (.Pair rh rt) table = .ok (some result, output) ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧ Preserves world final guards ∧
      (∃ outputOwners, Footprint final.memory packet.1 outputOwners ∧
        OwnerFrame final (outputOwners ++ (callerOwners final callers ++ external)) ∧
        BoxCoverage final (outputOwners ++ (callerOwners final callers ++ external))) ∧
      Evaluation minimumFuel (.Pair lh lt) (.Pair rh rt) table (some result) output cost ∧
      ResultOwnersAbove world.memory.length final.memory packet.1 ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Recursive.original budget fuel world guards callers .evaluate
          (inputPackets leftCell rightCell tableCell (.Pair lh lt) (.Pair rh rt) table) = some (final, packet, cost) := by
  dsimp only
  obtain ⟨entered, active, fuel, budget, middle, after, cell, work, entryRun, machine, state, bodyRun, empty, separate, fresh, kept, resultFresh⟩ :=
    entry_pair_successful_body_complete hw hc view lh lt rh rt table afterHeads afterTails heads tails subtotal total
      leftCell rightCell tableCell leftRead rightRead tableRead input frame covered miss headsTotal tailsTotal headSuccess tailSuccess
      subtotalSuccess rootSuccess leftTotal left afterLeft leftSuccess rightTotal right afterRight rightSuccess
  have native := pair_successful_native lh lt rh rt table afterHeads afterTails afterLeft afterRight heads tails left right subtotal total
    miss headSuccess tailSuccess subtotalSuccess rootSuccess leftSuccess rightSuccess
  obtain ⟨final, packet, value, readable, wf, preserved, owned, evaluation, provenance, stable⟩ :=
    evaluator_body_close_total_fresh (.Pair lh lt) (.Pair rh rt) table leftCell rightCell tableCell fuel budget cell work
      (some (selectedWitness (matchedWitness heads tails total) left right))
      (.Entry ⟨.Pair lh lt, .Pair rh rt, selectedWitness (matchedWitness heads tails total) left right⟩ afterRight)
      entryRun machine state bodyRun empty separate fresh kept protectedReads native resultFresh
  exact ⟨fuel + 1, budget, final, packet, _, value, native, readable, wf, preserved, owned, evaluation, provenance, stable⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
