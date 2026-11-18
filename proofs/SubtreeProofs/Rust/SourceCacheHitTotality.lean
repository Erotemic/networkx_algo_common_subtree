module

public import SubtreeProofs.Rust.SourceCacheHitOwnerProvenance
public import SubtreeProofs.Rust.SourceCloseTotality
public import SubtreeProofs.Rust.SourceOwnerRecursive
public import SubtreeProofs.Rust.SourceRecursiveBudget

/-! Total actual parsed evaluator execution on native cache hits. Independent
readable inputs and complete ownership construct entry, the helper lookup,
selected branch, return and checked closure. Shared aliases are permitted;
cache soundness and a desired successful physical run are not premises. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem cache_hit_total_fresh {world : World} {callers : List Activation} {previous : Resources} {guards : List Nat}
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
    (result : CommonEmbedding) (hit : MemoizedOrderedSolver.findResult table left right = some result) :
    let packets := inputPackets leftCell rightCell tableCell left right table
    ∃ (minimumFuel minimumBudget : Nat) (final : World) (packet : ValueCell) (lookupCost : LookupSource.Cost),
      packet.2 = encodeOutput (some result) table ∧ lookupCost.events = (LookupEvents.lookup table left right).2 ∧
      memoized_common_embedding left right table = .ok (some result, table) ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧ Preserves world final guards ∧
      (∃ output, Footprint final.memory packet.1 output ∧
        OwnerFrame final (output ++ (callerOwners final callers ++ external)) ∧
        BoxCoverage final (output ++ (callerOwners final callers ++ external))) ∧
      ResultOwnersAbove world.memory.length final.memory packet.1 ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Recursive.original budget fuel world guards callers .evaluate packets = some (final, packet, hitRunCost lookupCost) := by
  dsimp only
  let packets := inputPackets leftCell rightCell tableCell left right table
  obtain ⟨entered, active, fuel, budget, middle, after, cell, work, entryRun, machine, state, bodyRun, empty, separate, fresh, kept, resultFresh⟩ :=
    entry_hit_body_complete_fresh hw hc view left right table leftCell rightCell tableCell leftRead rightRead tableRead input frame covered result
      (by rw [LookupEvents.lookup_value]; exact hit)
  have readable : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2 := by
    intro p member
    simp only [packets, inputPackets, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact leftRead
    · exact rightRead
    · exact tableRead
  have typed : SnapshotFieldsTyped [.reference (encodeWord left), .reference (encodeWord right), encodeTable table]
      (Types.inputs CallingCertificate.originalEvaluator.source.function) := by
    rw [CallingCertificate.originalEvaluator_spec.1]
    exact .cons (.shared (word_typed left)) (.cons (.shared (word_typed right)) (.cons (table_typed table) .nil))
  have locals : LocalsTyped CallingCertificate.originalEvaluator.locals active.state := by
    rw [state]
    exact Types.initial_typed typed CallingCertificate.originalEvaluator.boundary
  have respects := Recursive.original_typed_respects budget fuel
  have constraints := CallingCertificate.originalEvaluator.constraints
  rw [CallingCertificate.originalEvaluator_spec.2.2] at constraints
  have ready := Calling.readyFor_typed respects (Types.original_run_typed fuel) constraints
    machine.valid machine.callersValid machine.wellFormed locals
  have checked := Calling.exec_spec respects machine.valid machine.callersValid machine.wellFormed body ready bodyRun
  have flow := checked.2.2.2
  obtain ⟨output, footprint, finalFrame, finalCovered⟩ := Calling.exec_owner_resources respects (Recursive.original_owns budget fuel)
    machine.valid machine.callersValid machine.wellFormed body ready machine.ownerFrame machine.coverage bodyRun
  let packet : ValueCell := (cell, encodeOutput (some result) table)
  obtain ⟨final, closeRun, _, _, finalWellFormed, finalReadable, closeKept, retired, finalFootprint, outputFrame, outputCovered⟩ :=
    close_total (packet := packet) (guards := guards) (external := external)
      flow.active flow.callers flow.wellFormed separate
      (fun slot => by change (after.state slot).dropWork.boxes = 0; rw [empty slot]; simp only [Slot.dropWork])
      flow.packet (encodeOutput_typed (some result) table) (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil)))
      footprint finalFrame finalCovered
      (by intro suspended current; rw [current.unique (view.transport kept)]; exact protectedReads)
      (by intro slot binding hb suspended current borrowed
          have old := view.preserved_read_bound hw kept current binding.address (current.loans_subset_reads borrowed)
          have new := fresh slot binding hb
          omega)
  change close middle after callers guards packet = some final at closeRun
  have outputFresh := Derived.close_result_owner_provenance flow.active flow.callers flow.wellFormed
    flow.packet resultFresh closeRun
  have invokeRun : Calling.invoke (Recursive.original budget fuel) callers guards CallingCertificate.originalEvaluator world packets =
      some (final, packet, (Cost.entry .evaluate).plus work) := by
    simp only [Calling.invoke, CallingCertificate.originalEvaluator_spec.1, CallingCertificate.originalEvaluator_spec.2.2,
      packets, inputPackets, Types.inputs, List.length_cons, List.length_nil, Nat.reduceAdd, ite_true]
    change (do
      let (entered, active) ← enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount packets
      let (flow, work) ← Calling.exec (Recursive.original budget fuel) callers body entered active
      match flow with
      | .next _ _ => none
      | .returned middle after packet => do
        let final ← close middle after callers guards packet
        some (final, packet, (Cost.entry .evaluate).plus work)) = _
    rw [entryRun]
    simp only [bind, Option.bind]
    rw [bodyRun]
    change (do let final ← close middle after callers guards packet
               some (final, packet, (Cost.entry .evaluate).plus work)) = _
    rw [closeRun]
    rfl
  have guarded := Calling.guardedInvoke_complete (callee := Recursive.original budget fuel)
    (decl := CallingCertificate.originalEvaluator) (packets := packets) view.scan protectedReads
  have actual : Recursive.original budget (fuel + 1) world guards callers .evaluate packets =
      some (final, packet, (Cost.entry .evaluate).plus work) := by
    simp only [Recursive.original, Recursive.run, Recursive.interpreted, ite_true, CallingCertificate.evaluator_lookup, bind, Option.bind]
    change Calling.guardedInvoke (Recursive.original budget fuel) callers guards CallingCertificate.originalEvaluator world packets = _
    rw [guarded]
    exact invokeRun
  have sourceRun := source_of_exec fuel _ _ _ (by rw [← state]; exact checked.1)
  obtain ⟨lookupCost, sourceHit, events⟩ := cache_hit_source table left right result hit (lookupDepth table left right) (by rfl)
  have sameCost := (SourceEval.run_unique Certificate.original.body sourceRun sourceHit).2
  rw [sameCost] at actual
  refine ⟨fuel + 1, budget, final, packet, lookupCost, rfl, events, cache_hit_native table left right result hit,
    finalReadable, finalWellFormed, (kept.weaken protectedReads).trans closeKept,
    ⟨output, finalFootprint, outputFrame, outputCovered⟩, outputFresh, ?_⟩
  intro largerFuel largerBudget fuelBound budgetBound
  exact Recursive.original_enlarge fuelBound budgetBound actual

/-- The preceding native totality API retains exactly its original statement. -/
theorem cache_hit_total {world : World} {callers : List Activation} {previous : Resources} {guards : List Nat}
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
    (result : CommonEmbedding) (hit : MemoizedOrderedSolver.findResult table left right = some result) :
    let packets := inputPackets leftCell rightCell tableCell left right table
    ∃ (minimumFuel minimumBudget : Nat) (final : World) (packet : ValueCell) (lookupCost : LookupSource.Cost),
      packet.2 = encodeOutput (some result) table ∧ lookupCost.events = (LookupEvents.lookup table left right).2 ∧
      memoized_common_embedding left right table = .ok (some result, table) ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧ Preserves world final guards ∧
      (∃ output, Footprint final.memory packet.1 output ∧
        OwnerFrame final (output ++ (callerOwners final callers ++ external)) ∧
        BoxCoverage final (output ++ (callerOwners final callers ++ external))) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Recursive.original budget fuel world guards callers .evaluate packets = some (final, packet, hitRunCost lookupCost) := by
  dsimp only
  obtain ⟨fuel, budget, final, packet, lookupCost, value, events, native, readable, wf, kept, resources, _, stable⟩ :=
    cache_hit_total_fresh hw hc view left right table leftCell rightCell tableCell leftRead rightRead tableRead
      input frame covered protectedReads result hit
  exact ⟨fuel, budget, final, packet, lookupCost, value, events, native, readable, wf, kept, resources, stable⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
