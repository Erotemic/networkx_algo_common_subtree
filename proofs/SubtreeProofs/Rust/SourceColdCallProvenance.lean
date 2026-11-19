module

public import SubtreeProofs.Rust.SourceColdEvaluatorProvenance
public import SubtreeProofs.Rust.SourceStoredOwnerProvenance

/-! Whole-packet freshness survives the actual call's guarded result store.
Ownership-free argument packets are sufficient even when other active locals
own old Boxes; those locals belong to the actual suspended caller ledger. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage

theorem original_call_fresh_output_of_no_input_owners (fuel budget : Nat)
    {world final : World} {active after : Activation} {callers : List Activation}
    {function : Function} {args : List Operand} {slot : Nat} {cost : Cost} {external : List Nat}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (frame : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    (hready : ∀ current suspended packets masks, active.scan world = some current →
      scanCallers world callers = some suspended →
      Addressed.operands world active.roots (current.loans ++ suspended.reads) active.state args = some (packets, masks) →
      TypedReady world function packets ∧ FieldsFootprint world.memory (packets.map Prod.fst) [])
    (run : call (Recursive.original budget fuel) world active callers function args slot = some (final, after, cost)) :
    LocalOwnersAbove world.memory.length final after slot := by
  simp only [call, bind, Option.bind_eq_some_iff] at run
  obtain ⟨current, currentScan, suspended, callerScan, ⟨packets, masks⟩, arguments,
    remainder, remainderScan, binding, root, ⟨returned, packet, inner⟩, invoked,
    ⟨next, state⟩, stored, last⟩ := run
  cases last
  have currentFrame := (Activation.scan_spec ha currentScan).frame
  obtain ⟨_, _, graph, subset, middleFrame⟩ := Addressed.operands_spec currentFrame args arguments
  let middle : Activation := {active with state := masks}
  have middleValid : middle.Valid world := ⟨ha.1, _, middleFrame⟩
  have readable := packets_readable graph (fun address member => currentFrame.alive address (subset member))
  obtain ⟨ready, noOwners⟩ := hready current suspended packets masks currentScan callerScan arguments
  obtain ⟨inputOwners, inputFootprint, partition⟩ := operands_owners ha args arguments
  have empty : inputOwners = [] := inputFootprint.unique noOwners
  subst inputOwners
  have transfer : (active.owners world ++ (callerOwners world callers ++ external)).Perm
      (callerOwners world (middle :: callers) ++ external) := by
    simpa only [middle, callerOwners, List.flatMap_cons, List.nil_append, List.append_assoc] using
      partition.append_right (callerOwners world callers ++ external)
  have suspendedValid : ∀ caller ∈ middle :: callers, caller.Valid world := by
    intro caller member
    rcases List.mem_cons.mp member with rfl | old
    · exact middleValid
    · exact hc caller old
  obtain ⟨all, scanned, guardsCovered⟩ := middle.call_guards_covered middleValid remainderScan callerScan root
  have view := scanCallers_spec suspendedValid scanned
  have alive : AliveOn world.live ((remainder.reads ++ suspended.reads) ++ [binding.address]) :=
    fun address member => view.alive address (guardsCovered member)
  obtain ⟨owners, footprint, _, _, fresh, _⟩ := Recursive.original_fresh_output_of_no_input_owners budget fuel
    hw suspendedValid readable ready view alive noOwners (frame.perm transfer) (covered.perm transfer) invoked
  obtain ⟨_, packetRead, _, _⟩ := Recursive.original_typed_respects budget fuel world _ (middle :: callers)
    function packets returned packet inner hw readable suspendedValid alive ready invoked
  have storedOwners := store_local_owners packetRead footprint stored
  intro resources represented address member
  exact fresh address ((storedOwners resources represented) ▸ member)

end SubtreeProofs.Rust.SourceEval.Addressed.Derived

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem cold_packets_no_owners {world : World} {packets : List ValueCell} (left right : BalancedWord)
    (readable : ∀ packet ∈ packets, Readable world.memory world.live packet.1 packet.2)
    (values : packets.map Prod.snd = [.reference (encodeWord left), .reference (encodeWord right), encodeTable .Empty]) :
    FieldsFootprint world.memory (packets.map Prod.fst) [] := by
  obtain ⟨first, second, third, rfl⟩ := Derived.packets_three_values values
  obtain ⟨_, one, _⟩ := readable (first, .reference (encodeWord left)) (by simp)
  obtain ⟨_, two, _⟩ := readable (second, .reference (encodeWord right)) (by simp)
  obtain ⟨_, three, _⟩ := readable (third, encodeTable .Empty) (by simp)
  cases one with | shared _ _ => cases two with | shared _ _ => cases three with
    | node fields => cases fields; exact .cons (.shared _) (.cons (.shared _) (.cons (.node .nil) .nil))

end SubtreeProofs.Rust.SourceEval.Evaluator
