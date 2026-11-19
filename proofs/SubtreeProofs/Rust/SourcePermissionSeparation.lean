module

public import SubtreeProofs.Rust.SourceReadPartition
public import SubtreeProofs.Rust.SourceOwnerRetirement
public import SubtreeProofs.Rust.SourceActivationInitial

/-! Owner uniqueness and classified stack roots discharge the non-loan part of
physical read separation. Fresh entry roots are separate from actual callers,
even if symbolic frame identifiers coincide. Shared-loan permissions remain
explicit and concern actual represented loans, not a desired successful step. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open Heap

def Activation.RootsSeparate (active : Activation) (callers : List Activation) : Prop :=
  ∀ slot binding, active.roots slot = some binding →
    ∀ caller ∈ callers, ∀ other target, caller.roots other = some target → binding.address ≠ target.address

theorem Activation.binding_lt {world : World} {active : Activation} (ha : active.Valid world)
    {slot : Nat} {binding : Binding} (hr : active.roots slot = some binding) : binding.address < world.memory.length := by
  obtain ⟨_, hf⟩ := ha.2
  obtain ⟨cell, _, hc, _⟩ := hf.get hr
  exact (List.getElem?_eq_some_iff.mp hc).choose

theorem Activation.rootsSeparate_of_fresh {world : World} {active : Activation} {callers : List Activation}
    (hc : ∀ caller ∈ callers, caller.Valid world)
    (fresh : ∀ slot binding, active.roots slot = some binding → world.memory.length ≤ binding.address) :
    active.RootsSeparate callers := by
  intro slot binding hr caller hm other target ht
  have old := Activation.binding_lt (hc caller hm) ht
  have new := fresh slot binding hr
  omega

theorem initialActivation_rootsSeparate {world : World} {callers : List Activation}
    (hc : ∀ caller ∈ callers, caller.Valid world) (frame count : Nat) (packets : List SourceEval.Addressed.ValueCell) :
    (initialActivation world frame count packets).RootsSeparate callers := by
  apply Activation.rootsSeparate_of_fresh hc
  intro slot binding hr
  simp only [initialActivation, argumentRoots] at hr
  split at hr
  next => cases hr; change world.memory.length ≤ world.memory.length + (slot - 1); omega
  next => cases hr

theorem Activation.RootsSeparate.set_fresh {world : World} {active : Activation} {callers : List Activation}
    (h : active.RootsSeparate callers) (hc : ∀ caller ∈ callers, caller.Valid world)
    (slot : Nat) (binding : Binding) (fresh : world.memory.length ≤ binding.address) :
    ({active with roots := active.roots.set slot (some binding)} : Activation).RootsSeparate callers := by
  intro index actual hr caller hm other target ht
  by_cases same : index = slot
  · subst index
    simp only [Roots.set, ite_true] at hr
    cases hr
    have old := Activation.binding_lt (hc caller hm) ht
    omega
  · simp only [Roots.set, same, ite_false] at hr
    exact h index actual hr caller hm other target ht

theorem Activation.RootsSeparate.erase {active : Activation} {callers : List Activation}
    (h : active.RootsSeparate callers) (slot : Nat) :
    ({active with roots := active.roots.set slot none} : Activation).RootsSeparate callers := by
  intro index binding hr caller hm other target ht
  by_cases same : index = slot
  · subst index; simp only [Roots.set, ite_true] at hr; cases hr
  · exact h index binding (by simpa only [Roots.set, same, ite_false] using hr) caller hm other target ht

theorem Inventory.owner_read_disjoint {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals}
    {slots : List Nat} {r : Resources} (h : Inventory world frame roots state slots r)
    {owners : List Nat} (boxes : BoxOwners world owners)
    (unique : List.Disjoint owners r.owners) (loans : List.Disjoint owners r.loans) :
    List.Disjoint owners r.reads := by
  apply List.disjoint_left.mpr
  intro address ho hr
  rcases h.read_cases hr with owned | borrowed | ⟨slot, hs, binding, hb, he⟩
  · exact List.disjoint_left.mp unique ho owned
  · exact List.disjoint_left.mp loans ho borrowed
  · obtain ⟨item, hl, _, _, _⟩ := h.get hs
    obtain ⟨_, _, _, classified, _, _⟩ := hl.anchored hb
    subst address
    exact boxes.stack_disjoint classified ho

theorem Callers.owner_read_disjoint {world : World} {callers : List Activation} {r : Resources}
    (h : Callers world callers r) {owners : List Nat} (boxes : BoxOwners world owners)
    (unique : List.Disjoint owners r.owners) (loans : List.Disjoint owners r.loans) :
    List.Disjoint owners r.reads := by
  apply List.disjoint_left.mpr
  intro address ho hr
  rcases h.read_cases hr with owned | borrowed | ⟨caller, hm, slot, binding, hb, he⟩
  · exact List.disjoint_left.mp unique ho owned
  · exact List.disjoint_left.mp loans ho borrowed
  · obtain ⟨_, current, _, _, _⟩ := h.get hm
    obtain ⟨_, _, _, classified, _, _⟩ := current.frame.get hb
    subst address
    exact boxes.stack_disjoint classified ho

theorem Activation.context_root_not_read {world : World} {active : Activation} (ha : active.Valid world)
    {slot : Nat} {binding : Binding} (hr : active.roots slot = some binding)
    {r : Resources} (h : Inventory world active.frame active.roots active.state (remainingSlots active.count slot) r)
    (boxes : BoxOwners world r.owners) (loans : binding.address ∉ r.loans) : binding.address ∉ r.reads := by
  obtain ⟨_, hf⟩ := ha.2
  obtain ⟨_, _, _, classified, _, _⟩ := hf.get hr
  intro read
  rcases h.read_cases read with owned | borrowed | ⟨other, hm, target, hb, he⟩
  · exact boxes.stack_disjoint classified owned
  · exact loans borrowed
  · obtain ⟨_, _, _, otherClass, _, _⟩ := hf.get hb
    rw [he] at classified
    have same := (Class.stack.inj (Option.some.inj (classified.symm.trans otherClass))).2.1
    have different := (List.mem_filter.mp hm).2
    rw [← same] at different
    simp at different

theorem Activation.RootsSeparate.caller_root_not_read {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (separate : active.RootsSeparate callers)
    {slot : Nat} {binding : Binding} (hr : active.roots slot = some binding)
    {r : Resources} (h : Callers world callers r)
    (boxes : BoxOwners world r.owners) (loans : binding.address ∉ r.loans) : binding.address ∉ r.reads := by
  obtain ⟨_, hf⟩ := ha.2
  obtain ⟨_, _, _, classified, _, _⟩ := hf.get hr
  intro read
  rcases h.read_cases read with owned | borrowed | ⟨caller, hm, other, target, hb, he⟩
  · exact boxes.stack_disjoint classified owned
  · exact loans borrowed
  · exact separate slot binding hr caller hm other target hb he

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage
