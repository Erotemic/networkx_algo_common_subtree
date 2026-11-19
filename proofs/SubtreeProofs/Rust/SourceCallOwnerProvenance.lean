module

public import SubtreeProofs.Rust.SourceResultPrefixProvenance

/-! Checked calls retain the canonical owner identities of untouched locals.
Helper allocation ledgers also retain bounds on transferred input owners, which
covers boxNew's fresh shell together with an independently bounded payload. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage

theorem call_keeps_owner_provenance {callee : Callees} {sourceCall : Calls} {ready : Ready}
    (respects : CallsRespect callee sourceCall ready)
    {world final : World} {active after : Activation} {callers : List Activation}
    {function : Function} {args : List Operand} {destination other bound : Nat} {cost : Cost}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (hready : ∀ current suspended packets masks, active.scan world = some current →
      scanCallers world callers = some suspended →
      Addressed.operands world active.roots (current.loans ++ suspended.reads) active.state args = some (packets, masks) →
      ready world function packets)
    (bounded : other < active.count) (safe : LocalPreservation.action other (.call function args destination) = true)
    (above : LocalOwnersAbove bound world active other)
    (run : call callee world active callers function args destination = some (final, after, cost)) :
    LocalOwnersAbove bound final after other := by
  have parts := Bool.and_eq_true_iff.mp safe
  have actual := run
  simp only [call, bind, Option.bind_eq_some_iff] at actual
  obtain ⟨current, currentScan, suspended, _, ⟨packets, masks⟩, arguments, remainder, _, binding, _,
    ⟨returned, packet, inner⟩, _, ⟨ending, state⟩, _, last⟩ := actual
  have frame := (Activation.scan_spec ha currentScan).frame
  obtain ⟨_, reflected, _, _, _⟩ := Addressed.operands_spec frame args arguments
  have maskSame := operands_local_same other parts.2 arguments
  obtain ⟨resources, _, represented⟩ := frame.inspectSlot other
  have kept := call_preserves_other_local respects ha hc hw function args destination hready reflected maskSame
    (of_decide_eq_true parts.1) bounded represented run
  have shape := call_shape run
  have next : LocalResources final after.frame after.roots after.state other resources := by
    rw [shape.1]
    exact (represented.transport kept).congr_at (congrFun shape.2.2 other) (call_local_same other safe run)
  exact LocalOwnersAbove.of_resource next (above resources represented)

theorem helper_call_owner_provenance (fuel budget : Nat) {world final : World} {active after : Activation}
    {callers : List Activation} {function : Function} {args : List Operand} {slot bound : Nat} {cost : Cost}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (oldBound : bound ≤ world.memory.length)
    (hready : ∀ current suspended packets masks, active.scan world = some current →
      scanCallers world callers = some suspended →
      Addressed.operands world active.roots (current.loans ++ suspended.reads) active.state args = some (packets, masks) →
      TypedReady world function packets)
    (inputs : OperandSourcesAbove bound world active args)
    (run : call (Helpers.callee fuel budget) world active callers function args slot = some (final, after, cost)) :
    LocalOwnersAbove bound final after slot := by
  simp only [call, bind, Option.bind_eq_some_iff] at run
  obtain ⟨current, currentScan, suspended, callerScan, ⟨packets, masks⟩, arguments,
    remainder, remainderScan, binding, root, ⟨returned, packet, inner⟩, invoked,
    ⟨next, state⟩, stored, last⟩ := run
  cases last
  have frame := (Activation.scan_spec ha currentScan).frame
  have callerFrame := scanCallers_spec hc callerScan
  obtain ⟨_, _, graph, subset, middleFrame⟩ := Addressed.operands_spec frame args arguments
  have middleValid : ({active with state := masks} : Activation).Valid world := ⟨ha.1, _, middleFrame⟩
  have context := Activation.context_spec middleValid slot remainderScan
  have alive : AliveOn world.live ((remainder.reads ++ suspended.reads) ++ [binding.address]) := by
    intro address member
    rcases List.mem_append.mp member with old | singleton
    · rcases List.mem_append.mp old with own | caller
      · exact context.alive address own
      · exact callerFrame.alive address caller
    · obtain ⟨_, _, _, _, _, included⟩ := middleFrame.get root
      exact middleFrame.alive address (included (List.mem_append_right _ singleton))
  have readable := packets_readable graph (fun address member => frame.alive address (subset member))
  have typed := hready current suspended packets masks currentScan callerScan arguments
  obtain ⟨inputOwners, inputFootprint, _⟩ := operands_owners ha args arguments
  have packetBounds := (operands_owner_provenance args ha arguments).2 inputs
  have inputBounds := fields_owner_provenance (by
    intro cell member
    obtain ⟨packet, selected, rfl⟩ := List.mem_map.mp member
    exact packetBounds packet selected) inputFootprint
  obtain ⟨owners, footprint, partition, _, _⟩ :=
    Helpers.callee_owner_ledger fuel budget hw function packets readable typed inputFootprint invoked
  have outputBounds : ∀ address ∈ owners, bound ≤ address := by
    intro address member
    rcases List.mem_append.mp (partition.subset member) with old | fresh
    · exact inputBounds address old
    · exact oldBound.trans (List.mem_range'_1.mp fresh).1
  obtain ⟨_, packetRead, _, _⟩ := Helpers.callee_typed_respects fuel budget world _ ({active with state := masks} :: callers)
    function packets returned packet inner hw readable
    (by intro caller member; rcases List.mem_cons.mp member with rfl | old; exact middleValid; exact hc caller old)
    alive typed invoked
  have exactOwners := store_local_owners packetRead footprint stored
  intro resources represented address member
  exact outputBounds address ((exactOwners resources represented) ▸ member)

theorem original_helper_call_owner_provenance (fuel budget : Nat) (positive : 0 < fuel)
    {world final : World} {active after : Activation} {callers : List Activation}
    {function : Function} {args : List Operand} {slot bound : Nat} {cost : Cost}
    (helper : Recursive.interpreted function = false)
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (oldBound : bound ≤ world.memory.length)
    (hready : ∀ current suspended packets masks, active.scan world = some current →
      scanCallers world callers = some suspended →
      Addressed.operands world active.roots (current.loans ++ suspended.reads) active.state args = some (packets, masks) →
      TypedReady world function packets)
    (inputs : OperandSourcesAbove bound world active args)
    (run : call (Recursive.original budget fuel) world active callers function args slot = some (final, after, cost)) :
    LocalOwnersAbove bound final after slot := by
  have same := call_callee_congr (Recursive.original budget fuel) (Helpers.callee fuel budget) function
    (Recursive.run_helper _ budget fuel positive function helper) world active callers args slot
  exact helper_call_owner_provenance fuel budget ha hc hw oldBound hready inputs (same.symm.trans run)

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
