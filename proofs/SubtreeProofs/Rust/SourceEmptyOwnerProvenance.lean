module

public import SubtreeProofs.Rust.SourceResultOwnerProvenance
public import SubtreeProofs.Rust.SourceEmptyTotality

/-! Complete actual empty-query cache-miss execution also identifies the
returned witness field's owner provenance. The updated table may retain old
owners; the existing totality statement and all its premises are preserved. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem empty_miss_total_fresh {world : World} {callers : List Activation} {previous : Resources} {guards : List Nat}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (left right : BalancedWord) (table : MemoTable) (leftCell rightCell tableCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord left)))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord right)))
    (tableRead : Readable world.memory world.live tableCell (encodeTable table))
    {owners external : List Nat}
    (input : FieldsFootprint world.memory [leftCell, rightCell, tableCell] owners)
    (frame : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (protectedReads : guards ⊆ previous.reads)
    (hempty : left = .Empty ∨ right = .Empty) (miss : MemoizedOrderedSolver.findResult table left right = none) :
    let packets := inputPackets leftCell rightCell tableCell left right table
    ∃ (minimumFuel minimumBudget : Nat) (final : World) (packet : ValueCell) (lookupCost insertCost : LookupSource.Cost),
      packet.2 = encodeOutput (some emptyWitness) (.Entry ⟨left, right, emptyWitness⟩ table) ∧ lookupCost.events = (LookupEvents.lookup table left right).2 ∧
      insertCost.events = MemoSource.insertEvents left right emptyWitness ∧
      memoized_common_embedding left right table = .ok (some emptyWitness, .Entry ⟨left, right, emptyWitness⟩ table) ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧ Preserves world final guards ∧
      (∃ output, Footprint final.memory packet.1 output ∧
        OwnerFrame final (output ++ (callerOwners final callers ++ external)) ∧
        BoxCoverage final (output ++ (callerOwners final callers ++ external))) ∧
      ResultOwnersAbove world.memory.length final.memory packet.1 ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Recursive.original budget fuel world guards callers .evaluate packets = some (final, packet, emptyRunCost left lookupCost insertCost) := by
  dsimp only
  obtain ⟨fuel, budget, final, packet, lookupCost, insertCost, value, lookupEvents, insertEvents, native,
    readable, wf, kept, resources, stable⟩ :=
    empty_miss_total hw hc view left right table leftCell rightCell tableCell leftRead rightRead tableRead
      input frame covered protectedReads hempty miss
  have packetRead := readable
  obtain ⟨reads, graph, _⟩ := packetRead
  rw [value] at graph
  have zero : (Slot.ofValue (encodeOption (some emptyWitness))).dropWork.boxes = 0 := by
    simp [emptyWitness, encodeOption, encodeResult, encodeWord, Slot.ofValue, ofFields, Slot.dropWork, dropFields, DropWork.plus]
  exact ⟨fuel, budget, final, packet, lookupCost, insertCost, value, lookupEvents, insertEvents, native,
    readable, wf, kept, resources, ResultOwnersAbove.of_zero graph zero, stable⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
