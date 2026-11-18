module

public import SubtreeProofs.Rust.SourceLoanSupport

/-! A closed owning local provides a precise loan anchor. Its reads consist
of its Box owners and its own stack root; every other current stack root is
excluded without excluding shared aliases into those owned Boxes. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open Heap

theorem LocalResources.owners_subset_activation {world : World} {active : Activation} {slot : Nat} {resources : Resources}
    (h : LocalResources world active.frame active.roots active.state slot resources) (bound : slot < active.count) :
    resources.owners ⊆ active.owners world := by
  have partition := active.owners_partition world slot bound h.source.ownerList
  exact fun _ member => partition.symm.subset (List.mem_append_left _ member)

theorem LocalResources.closed_reads_avoid_other_root {world : World} {active : Activation} {source slot : Nat} {resources : Resources}
    (h : LocalResources world active.frame active.roots active.state source resources) (valid : active.Valid world)
    {ty : Ty} (typed : SlotTyped (active.state source) ty) (closed : Borrow.Closed ty)
    (boxes : BoxOwners world resources.owners) {binding : Binding} (root : active.roots slot = some binding)
    (different : source ≠ slot) : binding.address ∉ resources.reads := by
  obtain ⟨_, frame⟩ := valid.2
  obtain ⟨_, _, _, classified, _, _⟩ := frame.get root
  intro member
  rcases h.read_cases member with owned | loan | ⟨target, bound, same⟩
  · exact boxes.stack_disjoint classified owned
  · rw [h.closed_loans typed closed] at loan
    cases loan
  · exact different (frame.distinct bound root same.symm)

theorem LocalResources.closed_reads_avoid_owners {world : World} {active : Activation} {source : Nat} {resources : Resources}
    (h : LocalResources world active.frame active.roots active.state source resources)
    {ty : Ty} (typed : SlotTyped (active.state source) ty) (closed : Borrow.Closed ty)
    {owners : List Nat} (boxes : BoxOwners world owners) (unique : List.Disjoint owners resources.owners) :
    List.Disjoint owners resources.reads := by
  apply List.disjoint_left.mpr
  intro address owned member
  rcases h.read_cases member with otherOwner | loan | ⟨binding, root, same⟩
  · exact List.disjoint_left.mp unique owned otherOwner
  · rw [h.closed_loans typed closed] at loan
    cases loan
  · obtain ⟨_, _, _, classified, _, _⟩ := h.anchored root
    subst address
    exact boxes.stack_disjoint classified owned

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem LoanSupport.reads_avoid_other_root {world : World} {active : Activation} {allowed : Nat → Prop} {index slot : Nat}
    (support : LoanSupport world active allowed index) (valid : active.Valid world)
    {binding : Binding} (root : active.roots slot = some binding) (different : index ≠ slot)
    (zero : (active.state index).dropWork.boxes = 0) (excluded : ¬ allowed binding.address)
    {resources : Resources} (represented : LocalResources world active.frame active.roots active.state index resources) :
    binding.address ∉ resources.reads := by
  intro member
  rcases represented.read_cases member with owned | borrowed | ⟨target, bound, same⟩
  · have empty := List.length_eq_zero_iff.mp (represented.boxes.trans zero)
    rw [empty] at owned
    cases owned
  · exact excluded (support.allows represented binding.address borrowed)
  · obtain ⟨_, frame⟩ := valid.2
    exact different (frame.distinct bound root same.symm)

theorem LoanSupport.write_other {world : World} {active : Activation} {allowed : Nat → Prop} {index slot : Nat}
    (support : LoanSupport world active allowed index) (valid : active.Valid world)
    {binding : Binding} (root : active.roots slot = some binding) (different : index ≠ slot)
    (zero : (active.state index).dropWork.boxes = 0) (excluded : ¬ allowed binding.address) (cell : Cell) :
    LoanSupport (world.write binding.address cell) active allowed index :=
  support.transport (fun _ represented => world.write_preserves
    (support.reads_avoid_other_root valid root different zero excluded represented) cell)

theorem LoanSupport.retire_other {world : World} {active : Activation} {allowed : Nat → Prop} {index slot : Nat}
    (support : LoanSupport world active allowed index) (valid : active.Valid world)
    {binding : Binding} (root : active.roots slot = some binding) (different : index ≠ slot)
    (zero : (active.state index).dropWork.boxes = 0) (excluded : ¬ allowed binding.address) :
    LoanSupport (world.retire [binding.address]) active allowed index := by
  apply support.transport
  intro resources represented
  apply Keeps.preserves
  apply world.retire_keeps
  intro address member retired
  have same := List.mem_singleton.mp retired
  subst address
  exact support.reads_avoid_other_root valid root different zero excluded represented member

end SubtreeProofs.Rust.SourceEval.Addressed
