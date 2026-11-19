module

public import SubtreeProofs.Rust.SourceStorageTotality

/-! Forward checked closure for closed result types. Source zero-owner masks,
actual complete ownership, root separation and represented caller-loan facts
establish cleanup; no successful close or supplied final world is a premise.
Symbolic retirement remains distinct from physical allocator deallocation. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open Heap

theorem close_complete_owned {world : World} {active : Activation} {callers : List Activation}
    {guards owners external : List Nat} {packet : SourceEval.Addressed.ValueCell} {ty : Ty}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world)
    (separate : active.RootsSeparate callers)
    (zero : ∀ slot, (active.state slot).dropWork.boxes = 0)
    (hp : Readable world.memory world.live packet.1 packet.2)
    (typed : SnapshotTyped packet.2 ty) (closed : Borrow.Closed ty)
    (ho : Footprint world.memory packet.1 owners)
    (hf : OwnerFrame world (owners ++ (active.owners world ++ (callerOwners world callers ++ external))))
    (guardSubset : ∀ suspended, Callers world callers suspended → guards ⊆ suspended.reads)
    (loans : ∀ slot binding, active.roots slot = some binding →
      ∀ suspended, Callers world callers suspended → binding.address ∉ suspended.loans) :
    close world active callers guards packet = some (world.retire active.stackAddresses) := by
  have outputBoxes : BoxOwners world owners := fun a hm => hf.classified a (List.mem_append_left _ hm)
  have callerBoxes : BoxOwners world (callerOwners world callers) := fun a hm =>
    hf.classified a (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hm)))
  apply close_complete ha hc
  · intro current scanned
    rw [← Activation.scan_owners ha scanned]
    exact Activation.owners_zero ha zero
  · exact hp
  · intro suspended used hs graph address hm
    have callerView := scanCallers_spec hc hs
    have callerClassified : BoxOwners world suspended.owners := by
      simpa only [callerView.owners] using callerBoxes
    obtain ⟨slot, binding, _, hb, rfl⟩ := Activation.mem_stackAddresses.mp hm
    have noCaller := Activation.RootsSeparate.caller_root_not_read ha separate hb callerView callerClassified
      (loans slot binding hb suspended callerView)
    obtain ⟨_, frame⟩ := ha.2
    obtain ⟨_, _, _, classified, _, _⟩ := frame.get hb
    have noOutput : binding.address ∉ used := by
      rw [graph.closed_reads typed closed ho]
      exact outputBoxes.stack_disjoint classified
    intro forbidden
    rcases List.mem_append.mp forbidden with old | output
    · rcases List.mem_append.mp old with guarded | read
      · exact noCaller (guardSubset suspended callerView guarded)
      · exact noCaller read
    · exact noOutput output

theorem close_total {world : World} {active : Activation} {callers : List Activation}
    {guards owners external : List Nat} {packet : SourceEval.Addressed.ValueCell} {ty : Ty}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (separate : active.RootsSeparate callers)
    (zero : ∀ slot, (active.state slot).dropWork.boxes = 0)
    (hp : Readable world.memory world.live packet.1 packet.2)
    (typed : SnapshotTyped packet.2 ty) (closed : Borrow.Closed ty)
    (ho : Footprint world.memory packet.1 owners)
    (hf : OwnerFrame world (owners ++ (active.owners world ++ (callerOwners world callers ++ external))))
    (covered : BoxCoverage world (owners ++ (active.owners world ++ (callerOwners world callers ++ external))))
    (guardSubset : ∀ suspended, Callers world callers suspended → guards ⊆ suspended.reads)
    (loans : ∀ slot binding, active.roots slot = some binding →
      ∀ suspended, Callers world callers suspended → binding.address ∉ suspended.loans) :
    ∃ final, close world active callers guards packet = some final ∧
      final.memory = world.memory ∧ final.classes = world.classes ∧ final.WellFormed ∧
      Readable final.memory final.live packet.1 packet.2 ∧ Preserves world final guards ∧
      (∀ slot binding, active.roots slot = some binding → final.live binding.address = false) ∧
      Footprint final.memory packet.1 owners ∧
      OwnerFrame final (owners ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (owners ++ (callerOwners final callers ++ external)) := by
  have run := close_complete_owned ha hc separate zero hp typed closed ho hf guardSubset loans
  obtain ⟨_, memory, classes, wf, readable, keeps, _, retired, _⟩ := close_spec ha hc hw hp run
  have resources := close_owner_transfer ha hc hw hp ho hf covered run
  exact ⟨_, run, memory, classes, wf, readable, keeps, retired, resources⟩

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage
