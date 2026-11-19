module

public import SubtreeProofs.Rust.SourceNoCallInvokeOwnerLedger
public import SubtreeProofs.Rust.SourceCallOwnerProvenance
public import SubtreeProofs.Rust.SourceChoiceCallTotality

/-! The real choice body has no calls: its returned owned identities come from
its actual input packet inventory. Guarded caller storage retains their bounds. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

namespace Recursive

theorem original_choice_owner_ledger (budget fuel : Nat) {world final : World} {callers : List Activation}
    {guards : List Nat} {packets : List ValueCell} {packet : ValueCell} {cost : Cost} {owners external : List Nat}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world)
    (readable : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (input : FieldsFootprint world.memory (packets.map Prod.fst) owners)
    (frame : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (run : original budget (fuel + 1) world guards callers .chooseLonger packets = some (final, packet, cost)) :
    ∃ output, Footprint final.memory packet.1 output ∧ output ⊆ owners := by
  have actual : Calling.guardedInvoke (original budget fuel) callers guards CallingCertificate.originalChoice world packets =
      some (final, packet, cost) := by
    simpa only [original, Recursive.run, interpreted, ite_true, CallingCertificate.choice_lookup, bind, Option.bind] using run
  exact Calling.guardedInvoke_noCalls_owner_ledger (original_typed_respects budget fuel) (original_owns budget fuel)
    CallingCertificate.originalChoice (by rw [CallingCertificate.originalChoice_spec.2.2]; decide +kernel)
    hw hc readable input frame covered actual

end Recursive

namespace Derived

theorem choice_call_owner_provenance (fuel budget : Nat) {world final : World} {active after : Activation}
    {callers : List Activation} {args : List Operand} {slot bound : Nat} {cost : Cost} {external : List Nat}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (frame : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    (hready : ∀ current suspended packets masks, active.scan world = some current →
      scanCallers world callers = some suspended →
      Addressed.operands world active.roots (current.loans ++ suspended.reads) active.state args = some (packets, masks) →
      TypedReady world .chooseLonger packets)
    (inputs : OperandSourcesAbove bound world active args)
    (run : call (Recursive.original budget fuel) world active callers .chooseLonger args slot = some (final, after, cost)) :
    LocalOwnersAbove bound final after slot := by
  simp only [call, bind, Option.bind_eq_some_iff] at run
  obtain ⟨current, currentScan, suspended, callerScan, ⟨packets, masks⟩, arguments,
    remainder, remainderScan, binding, root, ⟨returned, packet, inner⟩, invoked,
    ⟨next, state⟩, stored, last⟩ := run
  cases last
  have localFrame := (Activation.scan_spec ha currentScan).frame
  have callerFrame := scanCallers_spec hc callerScan
  obtain ⟨_, _, graph, subset, middleFrame⟩ := Addressed.operands_spec localFrame args arguments
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
  have readable := packets_readable graph (fun address member => localFrame.alive address (subset member))
  have typed := hready current suspended packets masks currentScan callerScan arguments
  obtain ⟨inputOwners, inputFootprint, partition⟩ := operands_owners ha args arguments
  have packetBounds := (operands_owner_provenance args ha arguments).2 inputs
  have inputBounds := fields_owner_provenance (by
    intro cell member
    obtain ⟨p, selected, rfl⟩ := List.mem_map.mp member
    exact packetBounds p selected) inputFootprint
  have transfer : (active.owners world ++ (callerOwners world callers ++ external)).Perm
      (inputOwners ++ (callerOwners world ({active with state := masks} :: callers) ++ external)) := by
    simpa only [callerOwners, List.flatMap_cons, List.append_assoc] using
      partition.append_right (callerOwners world callers ++ external)
  have callersValid : ∀ caller ∈ ({active with state := masks} :: callers), caller.Valid world := by
    intro caller member
    rcases List.mem_cons.mp member with rfl | old
    · exact middleValid
    · exact hc caller old
  obtain ⟨owners, footprint, included⟩ : ∃ owners, Footprint returned.memory packet.1 owners ∧ owners ⊆ inputOwners := by
    cases fuel with
    | zero => cases invoked
    | succ fuel =>
      exact Recursive.original_choice_owner_ledger budget fuel hw callersValid readable inputFootprint
        (frame.perm transfer) (covered.perm transfer) invoked
  have outputBounds : ∀ address ∈ owners, bound ≤ address := fun address member => inputBounds address (included member)
  obtain ⟨_, packetRead, _, _⟩ := Recursive.original_typed_respects budget fuel world _ ({active with state := masks} :: callers)
    .chooseLonger packets returned packet inner hw readable callersValid alive typed invoked
  have exactOwners := store_local_owners packetRead footprint stored
  intro resources represented address member
  exact outputBounds address ((exactOwners resources represented) ▸ member)

end Derived
end SubtreeProofs.Rust.SourceEval.Addressed
