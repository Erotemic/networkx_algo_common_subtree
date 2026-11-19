module

public import SubtreeProofs.Rust.SourceMaximumClosure

/-! Universal checked public maximum execution, including the actual cold table
teardown. The separate mathematical endpoint retains independent input-width
hypotheses; arbitrary finite execution keeps the native optional result. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Maximum

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem native_maximum_total_fresh {world : World} {callers : List Activation} {previous : Resources} {guards : List Nat}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (left right : BalancedWord) (leftCell rightCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord left)))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord right)))
    {external : List Nat} (frame : OwnerFrame world (callerOwners world callers ++ external))
    (covered : BoxCoverage world (callerOwners world callers ++ external))
    (protectedReads : guards ⊆ previous.reads) :
    ∃ minimumFuel minimumBudget final packet result cost owners,
      packet.2 = encodeOption result ∧ maximum_common_embedding left right = .ok result ∧
      SourceEval.run Certificate.original.body minimumFuel .maximum
        [.reference (encodeWord left), .reference (encodeWord right)] = some (packet.2, cost) ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧
      Preserves world final previous.reads ∧ Footprint final.memory packet.1 owners ∧
      OwnerFrame final (owners ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (owners ++ (callerOwners final callers ++ external)) ∧
      (∀ address ∈ owners, world.memory.length ≤ address) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Recursive.original budget fuel world guards callers .maximum (inputPackets leftCell rightCell left right) =
          some (final, packet, cost) ∧
        SourceEval.run Certificate.original.body fuel .maximum
          [.reference (encodeWord left), .reference (encodeWord right)] = some (packet.2, cost) := by
  obtain ⟨entered, active, fuel, budget, middle, after, cell, result, output, work,
    entry, machine, state, bodyRun, _, native, empty, separate, fresh, kept⟩ :=
    entry_body_complete hw hc view left right leftCell rightCell leftRead rightRead frame covered
  obtain ⟨final, packet, value, readable, wf, _, _, source, stable⟩ :=
    body_close_total left right leftCell rightCell fuel budget cell work result entry machine state bodyRun
      empty separate fresh kept protectedReads
  have inputsReadable : ∀ packet ∈ inputPackets leftCell rightCell left right,
      Readable world.memory world.live packet.1 packet.2 := by
    intro packet member
    simp only [inputPackets, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact leftRead
    · exact rightRead
  have typed : SnapshotFieldsTyped ((inputPackets leftCell rightCell left right).map Prod.snd) (Types.inputs .maximum) :=
    .cons (.shared (word_typed left)) (.cons (.shared (word_typed right)) .nil)
  have out : Types.callOutput .maximum (Types.inputs .maximum) = some (Types.output .maximum) := by
    simp only [Types.callOutput, reduceCtorEq, ite_false, SourceTypes.sameList_refl, ite_true]
  have input : FieldsFootprint world.memory ((inputPackets leftCell rightCell left right).map Prod.fst) [] := by
    obtain ⟨_, first, _⟩ := leftRead
    obtain ⟨_, second, _⟩ := rightRead
    cases first with | shared _ _ => cases second with | shared _ _ => exact .cons (.shared _) (.cons (.shared _) .nil)
  have alive : AliveOn world.live guards := fun address member => view.alive address (protectedReads member)
  obtain ⟨owners, footprint, owned, coverage, resultFresh, allKept⟩ :=
    Recursive.original_fresh_output_of_no_input_owners budget (fuel + 1) hw hc inputsReadable
      ⟨_, _, typed, out⟩ view alive input frame covered (stable (fuel + 1) budget (by rfl) (by rfl))
  refine ⟨fuel + 1, budget, final, packet, result, (Cost.entry .maximum).plus work, owners,
    value, native, source, readable, wf, allKept, footprint, owned, coverage, resultFresh, ?_⟩
  intro largerFuel largerBudget fuelBound budgetBound
  have actual := stable largerFuel largerBudget fuelBound budgetBound
  have source := (Recursive.original_typed_spec largerBudget largerFuel hw hc inputsReadable alive typed out actual).1
  exact ⟨actual, source⟩

theorem native_maximum_total_correct {world : World} {callers : List Activation} {previous : Resources} {guards : List Nat}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (left right : BalancedWord) (leftCell rightCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord left)))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord right)))
    {external : List Nat} (frame : OwnerFrame world (callerOwners world callers ++ external))
    (covered : BoxCoverage world (callerOwners world callers ++ external))
    (protectedReads : guards ⊆ previous.reads)
    (leftBound : (OrderedSolver.toDyck left).semilength < 2^32)
    (rightBound : (OrderedSolver.toDyck right).semilength < 2^32) :
    ∃ minimumFuel minimumBudget final packet witness cost owners,
      packet.2 = encodeOption (some witness) ∧ maximum_common_embedding left right = .ok (some witness) ∧
      Paper2004.OrderedTree.IsMaximumCommon
        (Paper2004.OrderedTree.decodeDyck (OrderedSolver.toDyck witness.word))
        (Paper2004.OrderedTree.decodeDyck (OrderedSolver.toDyck left))
        (Paper2004.OrderedTree.decodeDyck (OrderedSolver.toDyck right)) ∧
      witness.edges.val = (Paper2004.OrderedTree.decodeDyck (OrderedSolver.toDyck witness.word)).edgeCount ∧
      SourceEval.run Certificate.original.body minimumFuel .maximum
        [.reference (encodeWord left), .reference (encodeWord right)] = some (packet.2, cost) ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧
      Preserves world final previous.reads ∧ Footprint final.memory packet.1 owners ∧
      OwnerFrame final (owners ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (owners ++ (callerOwners final callers ++ external)) ∧
      (∀ address ∈ owners, world.memory.length ≤ address) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Recursive.original budget fuel world guards callers .maximum (inputPackets leftCell rightCell left right) =
          some (final, packet, cost) ∧
        SourceEval.run Certificate.original.body fuel .maximum
          [.reference (encodeWord left), .reference (encodeWord right)] = some (packet.2, cost) := by
  obtain ⟨fuel, budget, final, packet, result, cost, owners, value, native, source, readable, wf,
    kept, footprint, owned, coverage, fresh, stable⟩ :=
    native_maximum_total_fresh hw hc view left right leftCell rightCell leftRead rightRead frame covered protectedReads
  obtain ⟨witness, expected, maximum, score⟩ :=
    MemoizedOrderedSolver.maximum_common_embedding_correct left right leftBound rightBound
  have resultEq : result = some witness := Aeneas.Std.Result.ok_injective (native.symm.trans expected)
  subst result
  exact ⟨fuel, budget, final, packet, witness, cost, owners, value, native, maximum, score, source,
    readable, wf, kept, footprint, owned, coverage, fresh, stable⟩

end SubtreeProofs.Rust.SourceEval.Maximum
