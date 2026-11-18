module

public import SubtreeProofs.Rust.SourcePermissionSeparation

/-! Forward success of actual checked drops. Global owner uniqueness and Box
classification discharge owner checks and separate owners from stack roots.
Only independent live shared-loan and caller-root permissions remain explicit;
no successful drop, expected final world or post-step frame is assumed. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open Heap

theorem Inventory.context_owners {world : World} {active : Activation} {slot : Nat} {r : Resources}
    (h : Inventory world active.frame active.roots active.state (remainingSlots active.count slot) r) :
    (active.withoutLocal slot).owners world = r.owners := by
  change (ownerState world.memory (rawAt world (active.withoutLocal slot).roots) (active.withoutLocal slot).state).collect _ = _
  rw [Activation.withoutLocal_ownerState, OwnerState.collect_set_empty]
  exact h.owners

theorem Activation.partition_owner_frame {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding)
    {item remainder suspended : Resources}
    (localRep : LocalResources world active.frame active.roots active.state slot item)
    (remaining : Inventory world active.frame active.roots active.state (remainingSlots active.count slot) remainder)
    (callerView : Callers world callers suspended) :
    OwnerFrame world (item.owners ++ (remainder.owners ++ (suspended.owners ++ external))) := by
  have bound : slot < active.count := by
    by_contra hn
    have impossible := ha.1 slot (by omega)
    rw [hb] at impossible
    cases impossible
  have partition := active.owners_partition world slot bound localRep.source.ownerList
  have transferred := hf.perm (partition.append_right (callerOwners world callers ++ external))
  rw [remaining.context_owners, callerView.owners] at transferred
  simpa only [List.append_assoc] using transferred

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage

/-- A semantic permission on represented live loans in the current machine.
It makes no assertion about execution, owner uniqueness or allocation classes. -/
def DropLoansAllowed (world : World) (active : Activation) (callers : List Activation)
    (slot : Nat) (binding : Binding) : Prop :=
  ∀ item remainder suspended,
    LocalResources world active.frame active.roots active.state slot item →
    Inventory world active.frame active.roots active.state (remainingSlots active.count slot) remainder →
    Callers world callers suspended →
    List.Disjoint (binding.address :: item.owners) (remainder.loans ++ suspended.loans)

theorem drop_complete {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world)
    (separate : active.RootsSeparate callers) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding)
    (loans : DropLoansAllowed world active callers slot binding) :
    ∃ discarded, drop world active callers slot =
        some (world.retire discarded, {active with state := active.state.set slot .empty}) ∧
      destroyLocal world.memory (rawAt world active.roots slot) (active.state slot) =
        some (discarded, (active.state slot).dropWork) ∧
      discarded.length = (active.state slot).dropWork.boxes := by
  obtain ⟨current, _, scanned⟩ := active.scan_complete ha
  obtain ⟨item, hi, localRep⟩ := scanned.frame.inspectSlot slot
  obtain ⟨remainder, hr, remaining, _⟩ := active.context_complete ha slot
  obtain ⟨suspended, hs, callerView⟩ := scanCallers_complete callers hc
  have frame := Activation.partition_owner_frame ha hf hb localRep remaining callerView
  have itemBoxes : BoxOwners world item.owners := fun a hm => frame.classified a (List.mem_append_left _ hm)
  have remainingBoxes : BoxOwners world remainder.owners := fun a hm =>
    frame.classified a (List.mem_append_right _ (List.mem_append_left _ hm))
  have callerBoxes : BoxOwners world suspended.owners := fun a hm =>
    frame.classified a (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hm)))
  have remainingUnique : List.Disjoint item.owners remainder.owners := List.disjoint_left.mpr (by
    intro a hi hr
    exact List.disjoint_left.mp frame.unique.disjoint hi (List.mem_append_left _ hr))
  have callerUnique : List.Disjoint item.owners suspended.owners := List.disjoint_left.mpr (by
    intro a hi hs
    exact List.disjoint_left.mp frame.unique.disjoint hi (List.mem_append_right _ (List.mem_append_left _ hs)))
  have allowed := loans item remainder suspended localRep remaining callerView
  have remainingLoans : List.Disjoint item.owners remainder.loans := List.disjoint_left.mpr (by
    intro a hi hr
    exact List.disjoint_left.mp allowed (List.mem_cons_of_mem _ hi) (List.mem_append_left _ hr))
  have callerLoans : List.Disjoint item.owners suspended.loans := List.disjoint_left.mpr (by
    intro a hi hs
    exact List.disjoint_left.mp allowed (List.mem_cons_of_mem _ hi) (List.mem_append_right _ hs))
  have noRemainingRoot : binding.address ∉ remainder.loans := fun hm =>
    List.disjoint_left.mp allowed (by simp) (List.mem_append_left _ hm)
  have noCallerRoot : binding.address ∉ suspended.loans := fun hm =>
    List.disjoint_left.mp allowed (by simp) (List.mem_append_right _ hm)
  have noRemaining := remaining.owner_read_disjoint itemBoxes remainingUnique remainingLoans
  have noCaller := callerView.owner_read_disjoint itemBoxes callerUnique callerLoans
  have rootRemaining := Activation.context_root_not_read ha hb remaining remainingBoxes noRemainingRoot
  have rootCaller := Activation.RootsSeparate.caller_root_not_read ha separate hb callerView callerBoxes noCallerRoot
  have ready : item.owners.Nodup ∧ BoxOwners world item.owners ∧
      binding.address ∉ remainder.reads ++ suspended.reads ∧
      (∀ a ∈ remainder.reads ++ suspended.reads, a ∉ item.owners) := by
    refine ⟨frame.unique.of_append_left, itemBoxes, ?_, ?_⟩
    · simpa only [List.mem_append, not_or] using And.intro rootRemaining rootCaller
    · intro a hm ho
      rcases List.mem_append.mp hm with hm | hm
      · exact List.disjoint_left.mp noRemaining ho hm
      · exact List.disjoint_left.mp noCaller ho hm
  refine ⟨item.owners, ?_, localRep.source.destroy, localRep.boxes⟩
  simp only [drop, hi, scanContext, hr, hs, hb, bind, Option.bind]
  unfold BoxOwners at ready
  rw [ite_eq_left ready]

theorem drop_total {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (separate : active.RootsSeparate callers) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding)
    (loans : DropLoansAllowed world active callers slot binding) :
    ∃ discarded, drop world active callers slot =
        some (world.retire discarded, {active with state := active.state.set slot .empty}) ∧
      Step world active callers (.drop slot) (world.retire discarded)
        {active with state := active.state.set slot .empty} (Cost.local 1 (active.state slot).dropWork) ∧
      discarded.length = (active.state slot).dropWork.boxes ∧
      OwnerFrame (world.retire discarded)
        (({active with state := active.state.set slot .empty} : Activation).owners (world.retire discarded) ++
          (callerOwners (world.retire discarded) callers ++ external)) ∧
      BoxCoverage (world.retire discarded)
        (({active with state := active.state.set slot .empty} : Activation).owners (world.retire discarded) ++
          (callerOwners (world.retire discarded) callers ++ external)) := by
  obtain ⟨discarded, run, _, length⟩ := drop_complete ha hc separate hf hb loans
  obtain ⟨_, _, _, _, frame, coverage⟩ := drop_owner_resources ha hc hw hf covered run
  have step := (drop_spec ha hc hw run).1
  exact ⟨discarded, run, step, length, frame, coverage⟩

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
