module

public import SubtreeProofs.Rust.SourceStoredOwnerProvenance
public import SubtreeProofs.Rust.SourceRecursiveHelperCallTotality

/-! Actual copy, comparison, lookup, concatenation and checked-add helpers own
no input packet cells. Their existing complete allocation ledger therefore
locates every output Box after the incoming heap, including the guarded store. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

namespace Helpers

open LookupSource Heap Heap.Owners Partial Partial.Addressed Storage

def FreshOutputHelper (function : Function) : Prop :=
  function ∈ [.copyWord, .compare, .copyResult, .lookup, .concatenate, .checkedAdd]

theorem typed_plain_packets {world : World} {function : Function} {packets : List ValueCell}
    (selected : FreshOutputHelper function)
    (readable : ∀ packet ∈ packets, Readable world.memory world.live packet.1 packet.2)
    (ready : Derived.TypedReady world function packets) :
    FieldsFootprint world.memory (packets.map Prod.fst) [] := by
  obtain ⟨types, ty, typed, output⟩ := ready
  have different : function ≠ .boxNew := by intro same; subst function; simp [FreshOutputHelper] at selected
  have same := (Types.callOutput_standard different output).1
  rw [same] at typed
  have plain : ∀ ty ∈ Types.inputs function, ty = .boolean ∨ ty = .u32 ∨ ∃ inner, ty = .shared inner := by
    intro ty member
    cases function <;> simp_all [FreshOutputHelper, Types.inputs]
    rcases member with rfl | rfl <;> exact Or.inr (Or.inr ⟨_, rfl⟩)
  exact (((packets_represented readable).typed typed).plain_inputs plain).footprint _

theorem callee_fresh_output (fuel budget : Nat) {world final : World} {function : Function}
    {packets : List ValueCell} {guards : List Nat} {callers : List Activation} {packet : ValueCell} {cost : Cost}
    (hw : world.WellFormed) (selected : FreshOutputHelper function)
    (readable : ∀ packet ∈ packets, Readable world.memory world.live packet.1 packet.2)
    (ready : Derived.TypedReady world function packets)
    (run : callee fuel budget world guards callers function packets = some (final, packet, cost)) :
    ∃ owners, Footprint final.memory packet.1 owners ∧ ∀ address ∈ owners, world.memory.length ≤ address := by
  obtain ⟨owners, footprint, permutation, _, _⟩ :=
    callee_owner_ledger fuel budget hw function packets readable ready (typed_plain_packets selected readable ready) run
  refine ⟨owners, footprint, ?_⟩
  intro address member
  have freshMember : address ∈ fresh world.memory final.memory := by simpa using permutation.subset member
  exact (List.mem_range'_1.mp freshMember).1

end Helpers

namespace Derived

open LookupSource Heap Partial Partial.Addressed Storage

theorem helper_call_fresh_output (fuel budget : Nat) {world final : World} {active after : Activation}
    {callers : List Activation} {function : Function} {args : List Operand} {slot : Nat} {cost : Cost}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (selected : Helpers.FreshOutputHelper function)
    (hready : ∀ current suspended packets masks, active.scan world = some current →
      scanCallers world callers = some suspended →
      Addressed.operands world active.roots (current.loans ++ suspended.reads) active.state args = some (packets, masks) →
      TypedReady world function packets)
    (run : call (Helpers.callee fuel budget) world active callers function args slot = some (final, after, cost)) :
    LocalOwnersAbove world.memory.length final after slot := by
  simp only [call, bind, Option.bind_eq_some_iff] at run
  obtain ⟨current, currentScan, suspended, callerScan, ⟨packets, masks⟩, arguments,
    remainder, remainderScan, binding, bound, ⟨returned, packet, inner⟩, actual,
    ⟨next, state⟩, stored, last⟩ := run
  cases last
  have currentFrame := (Activation.scan_spec ha currentScan).frame
  have callerFrame := scanCallers_spec hc callerScan
  obtain ⟨_, _, graph, subset, middleFrame⟩ := Addressed.operands_spec currentFrame args arguments
  have middleValid : ({active with state := masks} : Activation).Valid world := ⟨ha.1, _, middleFrame⟩
  have context := Activation.context_spec middleValid slot remainderScan
  have alive : AliveOn world.live ((remainder.reads ++ suspended.reads) ++ [binding.address]) := by
    intro address member
    rcases List.mem_append.mp member with old | root
    · rcases List.mem_append.mp old with own | caller
      · exact context.alive address own
      · exact callerFrame.alive address caller
    · obtain ⟨_, _, _, _, _, included⟩ := middleFrame.get bound
      exact middleFrame.alive address (included (List.mem_append_right _ root))
  have readable := packets_readable graph (fun address member => currentFrame.alive address (subset member))
  have ready := hready current suspended packets masks currentScan callerScan arguments
  obtain ⟨owners, footprint, fresh⟩ := Helpers.callee_fresh_output fuel budget hw selected readable ready actual
  obtain ⟨_, packetRead, _, _⟩ := Helpers.callee_typed_respects fuel budget world _ ({active with state := masks} :: callers)
    function packets returned packet inner hw readable
    (by intro caller member; rcases List.mem_cons.mp member with rfl | old; exact middleValid; exact hc caller old)
    alive ready actual
  have storedOwners := store_local_owners packetRead footprint stored
  intro resources represented address member
  exact fresh address ((storedOwners resources represented) ▸ member)

theorem original_helper_call_fresh_output (fuel budget : Nat) (positive : 0 < fuel)
    {world final : World} {active after : Activation} {callers : List Activation}
    {function : Function} {args : List Operand} {slot : Nat} {cost : Cost}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (selected : Helpers.FreshOutputHelper function)
    (hready : ∀ current suspended packets masks, active.scan world = some current →
      scanCallers world callers = some suspended →
      Addressed.operands world active.roots (current.loans ++ suspended.reads) active.state args = some (packets, masks) →
      TypedReady world function packets)
    (run : call (Recursive.original budget fuel) world active callers function args slot = some (final, after, cost)) :
    LocalOwnersAbove world.memory.length final after slot := by
  have helper : Recursive.interpreted function = false := by
    cases function <;> simp_all [Helpers.FreshOutputHelper, Recursive.interpreted]
  have same := call_callee_congr (Recursive.original budget fuel) (Helpers.callee fuel budget) function
    (Recursive.run_helper _ budget fuel positive function helper) world active callers args slot
  exact helper_call_fresh_output fuel budget ha hc hw selected hready (same.symm.trans run)

end Derived
end SubtreeProofs.Rust.SourceEval.Addressed
