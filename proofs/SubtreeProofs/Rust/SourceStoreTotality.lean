module

public import SubtreeProofs.Rust.SourceLoanPermissions
public import SubtreeProofs.Rust.SourceOwnerCallTransfer

/-! Forward guarded stores for arbitrary readable packets, including shared
references. Owner classes discharge owned read conflicts; only actual shared
loans need destination separation. No stored result or successful store is an
input. Closed types discharge the packet-loan condition as a special case. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open Heap

theorem OwnerFrame.of_append_right {world : World} {first second : List Nat}
    (h : OwnerFrame world (first ++ second)) : OwnerFrame world second :=
  ⟨h.unique.of_append_right, fun a ha => h.classified a (List.mem_append_right _ ha),
    fun a ha => h.alive a (List.mem_append_right _ ha)⟩

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open Heap Storage

theorem Graph.stack_root_not_read {world : World} {cell : Cell} {value : Value} {reads owners : List Nat}
    (h : Graph world.memory cell value reads) (footprint : Footprint world.memory cell owners)
    (boxes : BoxOwners world owners) {address frame slot generation : Nat}
    (stack : world.classes address = some (.stack frame slot generation))
    (loans : ∀ borrowed, BorrowFootprint world.memory cell (Slot.ofValue value) borrowed → address ∉ borrowed) :
    address ∉ reads := by
  obtain ⟨r, _, sameReads, represented⟩ := h.partial.resources
  have sameOwners := Rep.unique represented.owned (Rep.of_full h.represents footprint)
  intro member
  have actual : address ∈ r.reads := by rw [sameReads]; exact member
  rcases List.mem_append.mp (represented.read_partition.subset actual) with owned | borrowed
  · rw [sameOwners] at owned
    exact boxes.stack_disjoint stack owned
  · exact loans r.loans represented.borrowed borrowed

end SubtreeProofs.Rust.LookupSource.Partial.Addressed

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage

def PacketLoansAvoid (world : World) (packet : ValueCell) (address : Nat) : Prop :=
  ∀ borrowed, BorrowFootprint world.memory packet.1 (Slot.ofValue packet.2) borrowed → address ∉ borrowed

def StoreLoansAllowed (world : World) (active : Activation) (callers : List Activation)
    (slot : Nat) (binding : Binding) (packet : ValueCell) : Prop :=
  ∀ remainder suspended borrowed,
    Inventory world active.frame active.roots active.state (remainingSlots active.count slot) remainder →
    Callers world callers suspended → BorrowFootprint world.memory packet.1 (Slot.ofValue packet.2) borrowed →
    binding.address ∉ remainder.loans ++ suspended.loans ++ borrowed

theorem PacketLoansAvoid.of_closed {world : World} {packet : ValueCell} {address : Nat} {ty : Ty}
    (typed : SnapshotTyped packet.2 ty) (closed : Borrow.Closed ty) : PacketLoansAvoid world packet address := by
  intro borrowed represented member
  rw [represented.closed_loans (ofValue_typed typed) closed] at member
  cases member

theorem StoreLoansAllowed.of_parts {world : World} {active : Activation} {callers : List Activation}
    {slot : Nat} {binding : Binding} {packet : ValueCell}
    (roots : RootLoansAllowed world active callers slot binding) (packetLoans : PacketLoansAvoid world packet binding.address) :
    StoreLoansAllowed world active callers slot binding packet := by
  intro remainder suspended borrowed remaining callers packetRep forbidden
  rcases List.mem_append.mp forbidden with old | payload
  · exact roots remainder suspended remaining callers old
  · exact packetLoans borrowed packetRep payload

theorem StoreLoansAllowed.of_closed {world : World} {active : Activation} {callers : List Activation}
    {slot : Nat} {binding : Binding} {packet : ValueCell} {ty : Ty}
    (roots : RootLoansAllowed world active callers slot binding)
    (typed : SnapshotTyped packet.2 ty) (closed : Borrow.Closed ty) :
    StoreLoansAllowed world active callers slot binding packet :=
  .of_parts roots (.of_closed typed closed)

theorem store_complete {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hw : world.WellFormed) (separate : active.RootsSeparate callers)
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding) (empty : active.state slot = .empty)
    {packet : ValueCell} {owners external : List Nat}
    (hp : Readable world.memory world.live packet.1 packet.2) (ho : Footprint world.memory packet.1 owners)
    (hf : OwnerFrame world (owners ++ (active.owners world ++ (callerOwners world callers ++ external))))
    {remainder suspended : Resources}
    (remaining : Inventory world active.frame active.roots active.state (remainingSlots active.count slot) remainder)
    (callerView : Callers world callers suspended)
    (loans : StoreLoansAllowed world active callers slot binding packet) :
    store world active.roots active.frame slot (remainder.reads ++ suspended.reads) active.state packet =
      some (world.write binding.address packet.1, active.state.set slot (Slot.ofValue packet.2)) := by
  obtain ⟨_, frame⟩ := ha.2
  obtain ⟨item, _, localRep⟩ := frame.inspectSlot slot
  have contextOwners := Activation.partition_owner_frame ha hf.of_append_right hb localRep remaining callerView
  have remainingBoxes : BoxOwners world remainder.owners := fun a hm =>
    contextOwners.classified a (List.mem_append_right _ (List.mem_append_left _ hm))
  have callerBoxes : BoxOwners world suspended.owners := fun a hm =>
    contextOwners.classified a (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hm)))
  have packetBoxes : BoxOwners world owners := fun a hm => hf.classified a (List.mem_append_left _ hm)
  obtain ⟨used, graph, _⟩ := hp
  obtain ⟨packetResources, _, _, represented⟩ := graph.partial.resources
  have allowed := loans remainder suspended packetResources.loans remaining callerView represented.borrowed
  have noRemainingLoan : binding.address ∉ remainder.loans := fun hm =>
    allowed (List.mem_append_left _ (List.mem_append_left _ hm))
  have noCallerLoan : binding.address ∉ suspended.loans := fun hm =>
    allowed (List.mem_append_left _ (List.mem_append_right _ hm))
  have noRemaining := Activation.context_root_not_read ha hb remaining remainingBoxes noRemainingLoan
  have noCaller := Activation.RootsSeparate.caller_root_not_read ha separate hb callerView callerBoxes noCallerLoan
  obtain ⟨_, _, _, classified, _, covered⟩ := frame.get hb
  have noPacket : binding.address ∉ used := by
    apply graph.stack_root_not_read ho packetBoxes classified
    intro borrowed packetRep hm
    exact loans remainder suspended borrowed remaining callerView packetRep (List.mem_append_right _ hm)
  have safe : binding.address ∉ (remainder.reads ++ suspended.reads) ++ used := by
    intro forbidden
    rcases List.mem_append.mp forbidden with old | payload
    · rcases List.mem_append.mp old with rem | caller
      · exact noRemaining rem
      · exact noCaller caller
    · exact noPacket payload
  have live := frame.alive binding.address (covered (List.mem_append_right _ (by simp)))
  have written := world.writeStack_success hw classified live safe packet.1
  simp only [store, empty, emptySlot, ite_true, hb, graph.trace, written, bind, Option.bind]

theorem store_total {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hw : world.WellFormed) (separate : active.RootsSeparate callers)
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding) (empty : active.state slot = .empty)
    {packet : ValueCell} {owners external : List Nat}
    (hp : Readable world.memory world.live packet.1 packet.2) (ho : Footprint world.memory packet.1 owners)
    (hf : OwnerFrame world (owners ++ (active.owners world ++ (callerOwners world callers ++ external))))
    (coverage : BoxCoverage world (owners ++ (active.owners world ++ (callerOwners world callers ++ external))))
    {remainder suspended : Resources}
    (remaining : Inventory world active.frame active.roots active.state (remainingSlots active.count slot) remainder)
    (callerView : Callers world callers suspended)
    (loans : StoreLoansAllowed world active callers slot binding packet) :
    ∃ final after, store world active.roots active.frame slot (remainder.reads ++ suspended.reads) active.state packet = some (final, after) ∧
      ({active with state := after} : Activation).Valid final ∧ final.WellFormed ∧
      (∀ caller ∈ callers, caller.Valid final) ∧ Preserves world final suspended.reads ∧
      OwnerFrame final (({active with state := after} : Activation).owners final ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (({active with state := after} : Activation).owners final ++ (callerOwners final callers ++ external)) := by
  have run := store_complete ha hw separate hb empty hp ho hf remaining callerView loans
  have context := Activation.context_spec ha slot remaining.inspect
  have extended := context.weaken (fun _ hm => List.mem_append_left suspended.reads hm) (by
    intro a hm
    rcases List.mem_append.mp hm with hm | hm
    · exact context.alive a hm
    · exact callerView.alive a hm)
  have stored := store_spec hw extended hp run
  have kept := stored.2.2.1.weaken (fun _ hm => List.mem_append_right remainder.reads hm)
  have callers := callerView.transport kept
  have resources := store_owner_resources hw ha.1 extended callerView (fun _ hm => List.mem_append_right _ hm) hp ho hf coverage run
  refine ⟨_, _, run, ⟨ha.1, stored.2.1⟩, stored.2.2.2, ?_, kept, resources⟩
  intro caller hm
  obtain ⟨_, current, _, _, _⟩ := callers.get hm
  exact current.valid

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
