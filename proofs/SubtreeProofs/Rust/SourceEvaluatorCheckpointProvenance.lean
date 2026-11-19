module

public import SubtreeProofs.Rust.SourceEvaluatorFreshCallTotality

/-! Recover witness owner provenance at actual recursive call checkpoints.
The stronger smaller-request contract is explicit. Actual argument scans and
stores supply their physical guards; no new forward loan permission or desired
post-frame is supplied to this retrospective transfer theorem. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage verified_ordered_core

theorem evaluator_checkpoint_fresh_spec {world final : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    (left right : BalancedWord) (table : MemoTable) (childTotal : Evaluator.NativeTotalFresh left right)
    {args : List Operand} {slot fuel budget : Nat} {masks : State} {cost : Cost}
    (source : SourceEval.operands active.state args =
      some ([.reference (encodeWord left), .reference (encodeWord right), encodeTable table], masks))
    (run : call (Recursive.original budget fuel) world active callers .evaluate args slot = some (final, after, cost)) :
    ∃ result output,
      after.state = masks.set slot (Slot.ofValue (Evaluator.encodeOutput result output)) ∧
      memoized_common_embedding left right table = .ok (result, output) ∧
      after.Valid final ∧ (∀ caller ∈ callers, caller.Valid final) ∧ final.WellFormed ∧
      LocalResultOwnersAbove world.memory.length final after slot := by
  have typed : SnapshotFieldsTyped [.reference (encodeWord left), .reference (encodeWord right), encodeTable table]
      [.shared (.adt .word), .shared (.adt .word), .adt .table] :=
    .cons (.shared (word_typed left)) (.cons (.shared (word_typed right)) (.cons (table_typed table) .nil))
  have outputType : Types.callOutput .evaluate [.shared (.adt .word), .shared (.adt .word), .adt .table] =
      some (.tuple [.adt .optional, .adt .table]) := by
    simp only [Types.callOutput, reduceCtorEq, ite_false, Types.inputs, SourceTypes.sameList_refl, ite_true, Types.output]
  have ready := call_ready_from_values (callers := callers) ha source typed outputType
  have spec := call_spec (Recursive.original_typed_respects budget fuel) ha hc hw .evaluate args slot ready run
  simp only [call, bind, Option.bind_eq_some_iff] at run
  obtain ⟨current, scan, suspended, callerScan, ⟨packets, actualMasks⟩, arguments,
    remainder, remainingScan, binding, root, ⟨returned, packet, inner⟩, invoked,
    ⟨ending, state⟩, stored, last⟩ := run
  cases last
  have scanned := Activation.scan_spec ha scan
  have callerView := scanCallers_spec hc callerScan
  obtain ⟨_, reflected, graph, subset, middleFrame⟩ := Addressed.operands_spec scanned.frame args arguments
  have same := Prod.mk.inj (Option.some.inj (reflected.symm.trans source))
  have valuesEq := same.1
  have masksEq := same.2
  subst actualMasks
  let middle : Activation := {active with state := masks}
  have middleValid : middle.Valid world := ⟨ha.1, _, middleFrame⟩
  obtain ⟨allResources, allScan, guardsCovered⟩ := middle.call_guards_covered middleValid remainingScan callerScan root
  have suspendedValid : ∀ caller ∈ middle :: callers, caller.Valid world := by
    intro caller member
    rcases List.mem_cons.mp member with rfl | old
    · exact middleValid
    · exact hc caller old
  have allView := scanCallers_spec suspendedValid allScan
  have readable := packets_readable graph (fun address member => scanned.frame.alive address (subset member))
  obtain ⟨owners, footprint, partition⟩ := operands_owners ha args arguments
  have transfer : (active.owners world ++ (callerOwners world callers ++ external)).Perm
      (owners ++ (callerOwners world (middle :: callers) ++ external)) := by
    simpa only [middle, callerOwners, List.flatMap_cons, List.append_assoc] using
      partition.append_right (callerOwners world callers ++ external)
  obtain ⟨firstCell, secondCell, thirdCell, packetShape⟩ := packets_three_values valuesEq
  subst packets
  obtain ⟨minimumFuel, minimumBudget, checkedWorld, checkedPacket, result, output, checkedCost,
    value, native, checkedRead, _, _, _, fresh, stable⟩ :=
    childTotal hw suspendedValid allView table firstCell secondCell thirdCell
      (readable (firstCell, .reference (encodeWord left)) (by simp))
      (readable (secondCell, .reference (encodeWord right)) (by simp))
      (readable (thirdCell, encodeTable table) (by simp)) footprint (hf.perm transfer) (covered.perm transfer) guardsCovered
  have actual := Recursive.original_enlarge (Nat.le_max_left fuel minimumFuel) (Nat.le_max_left budget minimumBudget) invoked
  have checked := stable (max fuel minimumFuel) (max budget minimumBudget) (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have equal := Prod.mk.inj (Option.some.inj (actual.symm.trans checked))
  obtain ⟨rfl, rfl, rfl⟩ := And.intro equal.1 (Prod.mk.inj equal.2)
  obtain ⟨reads, packetGraph, _⟩ := checkedRead
  obtain ⟨rawStored, retained⟩ := store_packet_kept packetGraph stored
  refine ⟨result, output, ?_, native, spec.2.2.2.2.1, spec.2.2.2.2.2.1, spec.2.2.2.2.2.2.1, ⟨_, rawStored, fresh.transport packetGraph retained⟩⟩
  change state = _
  rw [store_state stored, value]

theorem evaluator_checkpoint_owner_provenance {world final : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    (left right : BalancedWord) (table : MemoTable) (childTotal : Evaluator.NativeTotalFresh left right)
    {args : List Operand} {slot fuel budget : Nat} {masks : State} {cost : Cost}
    (source : SourceEval.operands active.state args =
      some ([.reference (encodeWord left), .reference (encodeWord right), encodeTable table], masks))
    (run : call (Recursive.original budget fuel) world active callers .evaluate args slot = some (final, after, cost)) :
    LocalResultOwnersAbove world.memory.length final after slot := by
  obtain ⟨_, _, _, _, _, _, _, fresh⟩ := evaluator_checkpoint_fresh_spec ha hc hw hf covered left right table childTotal source run
  exact fresh

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
