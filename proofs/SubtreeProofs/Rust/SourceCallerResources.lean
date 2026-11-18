module

public import SubtreeProofs.Rust.SourceActivationInventory

/-! Complete caller read inventories are deterministic, including transitive
reads and stack roots. Destination-excluding contexts and the actual destination
are covered by the complete post-argument suspended activation. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open Heap

theorem PartialGraph.guards_unique {memory : Memory} {cell : Cell} {part : Slot} {first second : List Nat}
    (h₁ : PartialGraph memory cell part first) (h₂ : PartialGraph memory cell part second) : first = second := by
  obtain ⟨a, ha, he, _⟩ := h₁.resources
  obtain ⟨b, hb, hf, _⟩ := h₂.resources
  have h := Option.some.inj (ha.symm.trans hb)
  subst b
  exact he.symm.trans hf

namespace Storage

theorem LocalResources.reads_unique {world : World} {frame slot : Nat} {roots : Roots} {state : Partial.Locals}
    {first second : Resources} (h₁ : LocalResources world frame roots state slot first)
    (h₂ : LocalResources world frame roots state slot second) : first.reads = second.reads := by
  cases h₁ with
  | vacant hr _ =>
    cases h₂ with
    | vacant _ _ => rfl
    | stored hs _ _ _ _ => rw [hr] at hs; cases hs
  | stored hr hc _ hv _ =>
    cases h₂ with
    | vacant hs _ => rw [hr] at hs; cases hs
    | stored hs hd _ hw _ =>
      have hb := Option.some.inj (hr.symm.trans hs)
      cases hb
      have he := Option.some.inj (hc.symm.trans hd)
      cases he
      exact congrArg (fun reads => reads ++ [_]) (hv.graph.guards_unique hw.graph)

theorem Inventory.reads_unique {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals} {slots : List Nat}
    {first second : Resources} (h₁ : Inventory world frame roots state slots first)
    (h₂ : Inventory world frame roots state slots second) : first.reads = second.reads := by
  induction h₁ generalizing second with
  | nil => cases h₂; rfl
  | cons head tail ih =>
    cases h₂ with
    | cons first rest =>
      exact congrArg₂ List.append (head.reads_unique first) (ih rest)

theorem Inventory.reads_subset {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals}
    {small large : List Nat} {first second : Resources} (h₁ : Inventory world frame roots state small first)
    (h₂ : Inventory world frame roots state large second) (hs : small ⊆ large) : first.reads ⊆ second.reads := by
  induction h₁ with
  | nil => simp
  | @cons slot slots head tail hi rest ih =>
    obtain ⟨item, hv, hr, _, _⟩ := h₂.get (hs (show slot ∈ slot :: slots by simp))
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hr (hi.reads_unique hv ▸ ha)
    · exact ih (fun _ hm => hs (List.mem_cons_of_mem _ hm)) ha

theorem Callers.reads_unique {world : World} {stack : List Activation} {first second : Resources}
    (h₁ : Callers world stack first) (h₂ : Callers world stack second) : first.reads = second.reads := by
  induction h₁ generalizing second with
  | nil => cases h₂; rfl
  | cons head tail ih =>
    cases h₂ with
    | cons first rest => exact congrArg₂ List.append (head.inventory.reads_unique first.inventory) (ih rest)

theorem Scanned.binding_reads {world : World} {active : Activation} {r : Resources}
    (h : Scanned world active r) {slot : Nat} {binding : Binding} (hr : active.roots slot = some binding) :
    binding.address ∈ r.reads := by
  obtain ⟨_, _, _, _, _, hs⟩ := h.frame.get hr
  exact hs (List.mem_append_right _ (by simp))

theorem Activation.context_reads_subset {world : World} {active : Activation} {full rest : Resources}
    (ha : active.Valid world) (hf : active.scan world = some full) (slot : Nat)
    (hr : active.scanExcept world slot = some rest) : rest.reads ⊆ full.reads := by
  obtain ⟨actual, hs, hi, _⟩ := active.context_complete ha slot
  have he := Option.some.inj (hs.symm.trans hr)
  subst actual
  exact hi.reads_subset (Activation.scan_spec ha hf).inventory (by
    intro a hm
    exact (List.mem_filter.mp hm).1)

theorem Activation.call_guards_covered {world : World} {active : Activation} {callers : List Activation}
    {rest suspended : Resources} {slot : Nat} {binding : Binding}
    (ha : active.Valid world) (hr : active.scanExcept world slot = some rest)
    (hs : scanCallers world callers = some suspended) (hb : active.roots slot = some binding) :
    ∃ all, scanCallers world (active :: callers) = some all ∧
      (rest.reads ++ suspended.reads) ++ [binding.address] ⊆ all.reads := by
  obtain ⟨full, hf, hv⟩ := active.scan_complete ha
  refine ⟨full.plus suspended, by simp only [scanCallers, hf, hs, Bind.bind, Option.bind], ?_⟩
  intro a hm
  rcases List.mem_append.mp hm with hm | hm
  · rcases List.mem_append.mp hm with hm | hm
    · exact List.mem_append_left _ (active.context_reads_subset ha hf slot hr hm)
    · exact List.mem_append_right _ hm
  · have he := List.mem_singleton.mp hm
    exact List.mem_append_left _ (he ▸ hv.binding_reads hb)

end Storage
end SubtreeProofs.Rust.LookupSource.Partial.Addressed
