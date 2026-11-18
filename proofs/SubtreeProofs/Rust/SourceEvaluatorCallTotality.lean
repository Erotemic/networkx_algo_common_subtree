module

public import SubtreeProofs.Rust.SourceEvaluatorNativeTotal
public import SubtreeProofs.Rust.SourceChoiceCallTotality

/-! Construct a whole evaluator call from the universal native contract for its
smaller query pair. The caller's arguments, scans, owner transfer, destination
store and stable fuel/readback bounds are derived here. No completed parent
call is assumed; the explicit smaller-request contract remains to be discharged
by the full pair/pair induction. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage verified_ordered_core

theorem packets_three_values {packets : List ValueCell} {first second third : Value}
    (values : packets.map Prod.snd = [first, second, third]) :
    ∃ firstCell secondCell thirdCell, packets = [(firstCell, first), (secondCell, second), (thirdCell, third)] := by
  have length : packets.length = 3 := by
    have same := congrArg List.length values
    simpa only [List.length_map, List.length_cons, List.length_nil] using same
  cases packets with
  | nil => cases length
  | cons firstPacket rest => cases rest with
    | nil => cases length
    | cons secondPacket rest => cases rest with
      | nil => cases length
      | cons thirdPacket rest => cases rest with
        | cons _ _ => simp only [List.length_cons] at length; omega
        | nil =>
          rcases firstPacket with ⟨firstCell, firstValue⟩
          rcases secondPacket with ⟨secondCell, secondValue⟩
          rcases thirdPacket with ⟨thirdCell, thirdValue⟩
          simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at values
          obtain ⟨rfl, rfl, rfl⟩ := values
          exact ⟨firstCell, secondCell, thirdCell, rfl⟩

theorem evaluator_call_total {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (separate : active.RootsSeparate callers) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    (left right : BalancedWord) (table : MemoTable) (childTotal : Evaluator.NativeTotal left right)
    (args : List Operand) {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding) {masks : State}
    (source : SourceEval.operands active.state args = some ([.reference (encodeWord left), .reference (encodeWord right), encodeTable table], masks))
    (empty : masks slot = .empty)
    (moves : ∀ current suspended, Scanned world active current → Callers world callers suspended →
      ∀ op ∈ args, Allowed world active.roots (current.loans ++ suspended.reads) op)
    (loans : RootLoansAllowed world {active with state := masks} callers slot binding) :
    ∃ minimumFuel minimumBudget final after result output cost,
      after.state = masks.set slot (Slot.ofValue (Evaluator.encodeOutput result output)) ∧
      memoized_common_embedding left right table = .ok (result, output) ∧
      after.Valid final ∧ final.WellFormed ∧ (∀ caller ∈ callers, caller.Valid final) ∧
      OwnerFrame final (after.owners final ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (after.owners final ++ (callerOwners final callers ++ external)) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        call (Recursive.original budget fuel) world active callers .evaluate args slot = some (final, after, cost) ∧
        SourceEval.action (SourceEval.run Certificate.original.body fuel) active.state (.call .evaluate args slot) = some (after.state, cost) := by
  obtain ⟨current, scan, scanned⟩ := active.scan_complete ha
  obtain ⟨suspended, callerScan, callerView⟩ := scanCallers_complete callers hc
  obtain ⟨packets, arguments, valuesEq⟩ := Addressed.operands_complete scanned.frame args source
    (moves current suspended scanned callerView)
  obtain ⟨_, _, graph, subset, middleFrame⟩ := Addressed.operands_spec scanned.frame args arguments
  let middle : Activation := {active with state := masks}
  have middleValid : middle.Valid world := ⟨ha.1, _, middleFrame⟩
  obtain ⟨remainder, remainingScan, remaining, _⟩ := middle.context_complete middleValid slot
  obtain ⟨allResources, allScan, guardsCovered⟩ := middle.call_guards_covered middleValid remainingScan callerScan hb
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
  obtain ⟨minimumFuel, minimumBudget, returned, packet, result, output, inner, nativeValue, native, packetRead, returnedWf, kept,
    ⟨outputOwners, outputFootprint, outputFrame, outputCoverage⟩, stable⟩ :=
    childTotal hw suspendedValid allView table firstCell secondCell thirdCell
      (readable (firstCell, .reference (encodeWord left)) (by simp))
      (readable (secondCell, .reference (encodeWord right)) (by simp))
      (readable (thirdCell, encodeTable table) (by simp)) footprint (hf.perm transfer) (covered.perm transfer) guardsCovered
  have retained := kept.weaken (fun _ member => List.mem_append_left _ member)
  have postValid := Activation.preserve_call_context middleValid hb empty remaining callerView kept
  have postRemaining := remaining.transport (retained.weaken (fun _ member => List.mem_append_left _ member))
  have postCallers := callerView.transport (retained.weaken (fun _ member => List.mem_append_right _ member))
  have postFrame : OwnerFrame returned (outputOwners ++ (middle.owners returned ++ (callerOwners returned callers ++ external))) := by
    simpa only [callerOwners, List.flatMap_cons, List.append_assoc] using outputFrame
  have typedOutput : SnapshotTyped packet.2 (.tuple [.adt .optional, .adt .table]) := by
    rw [nativeValue]; exact Evaluator.encodeOutput_typed result output
  have stored := store_complete postValid returnedWf separate hb empty packetRead outputFootprint postFrame
    postRemaining postCallers (StoreLoansAllowed.of_closed (loans.transport remaining callerView retained) typedOutput
      (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))))
  have execute : ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
      call (Recursive.original budget fuel) world active callers .evaluate args slot =
        some (returned.write binding.address packet.1, {active with state := masks.set slot (Slot.ofValue packet.2)},
          (Cost.local (Action.call .evaluate args slot).weight).plus inner) := by
    intro fuel budget fuelBound budgetBound
    exact call_run scan callerScan arguments remainingScan hb (stable fuel budget fuelBound budgetBound) stored
  have typed : SnapshotFieldsTyped [.reference (encodeWord left), .reference (encodeWord right), encodeTable table]
      [.shared (.adt .word), .shared (.adt .word), .adt .table] :=
    .cons (.shared (word_typed left)) (.cons (.shared (word_typed right)) (.cons (table_typed table) .nil))
  have outputType : Types.callOutput .evaluate [.shared (.adt .word), .shared (.adt .word), .adt .table] =
      some (.tuple [.adt .optional, .adt .table]) := by
    simp only [Types.callOutput, reduceCtorEq, ite_false, Types.inputs, SourceTypes.sameList_refl, ite_true, Types.output]
  have ready := call_ready_from_values (callers := callers) ha source typed outputType
  have firstRun := execute minimumFuel minimumBudget (by rfl) (by rfl)
  have spec := call_spec (Recursive.original_typed_respects minimumBudget minimumFuel) ha hc hw .evaluate args slot ready firstRun
  have resources := call_owner_resources (Recursive.original_typed_respects minimumBudget minimumFuel)
    (Recursive.original_owns minimumBudget minimumFuel) ha hc hw .evaluate args slot hf covered ready firstRun
  refine ⟨minimumFuel, minimumBudget, returned.write binding.address packet.1,
    {active with state := masks.set slot (Slot.ofValue packet.2)}, result, output,
    (Cost.local (Action.call .evaluate args slot).weight).plus inner, ?_, native,
    spec.2.2.2.2.1, spec.2.2.2.2.2.2.1, spec.2.2.2.2.2.1, resources.1, resources.2, ?_⟩
  · rw [nativeValue]
  · intro fuel budget fuelBound budgetBound
    have run := execute fuel budget fuelBound budgetBound
    exact ⟨run, (call_spec (Recursive.original_typed_respects budget fuel) ha hc hw .evaluate args slot ready run).1⟩

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
