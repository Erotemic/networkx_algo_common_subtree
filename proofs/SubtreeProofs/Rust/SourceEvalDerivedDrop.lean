module

public import SubtreeProofs.Rust.SourceEvalDerivedStorage

/-! A drop derives exact live Box owners and remaining/caller read guards from
the current partial frame. It checks owner classes, uniqueness, separation and
the affected stack root before clearing initialization. Stored bytes remain. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

mutual
  theorem Rep.subset_reads {memory : Heap.Memory} {cell : Heap.Cell} {part : Slot} {owners reads : List Nat}
      (h : Rep memory cell part owners) (hg : PartialGraph memory cell part reads) : owners ⊆ reads := by
    cases h with
    | empty _ | boolean _ | number _ | shared _ => simp
    | node fields => cases hg with | node data => exact fields.subset_reads data
    | owned hr child => cases hg with
      | owned hs data =>
        have he := Option.some.inj (hr.symm.trans hs)
        cases he
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact List.mem_append_left _ (child.subset_reads data ha)
        · exact List.mem_append_right _ ha

  theorem FieldsRep.subset_reads {memory : Heap.Memory} {cells : List Heap.Cell} {parts : List Slot} {owners reads : List Nat}
      (h : FieldsRep memory cells parts owners) (hg : PartialGraphFields memory cells parts reads) : owners ⊆ reads := by
    cases h with
    | nil => simp
    | cons first rest => cases hg with
      | cons data tail =>
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact List.mem_append_left _ (first.subset_reads data ha)
        · exact List.mem_append_right _ (rest.subset_reads tail ha)
end

theorem ResourceRep.owners_subset_reads {memory : Heap.Memory} {cell : Heap.Cell} {part : Slot} {r : Resources}
    (h : ResourceRep memory cell part r) : r.owners ⊆ r.reads := h.owned.subset_reads h.graph

namespace Storage

theorem LocalResources.owners_subset_reads {world : World} {frame slot : Nat} {roots : Roots} {state : Partial.Locals} {r : Resources}
    (h : LocalResources world frame roots state slot r) : r.owners ⊆ r.reads := by
  cases h with
  | vacant _ _ => simp
  | stored _ _ _ hv _ => exact fun _ ha => List.mem_append_left _ (hv.owners_subset_reads ha)

theorem Frame.inspectSlot_spec {world : World} {frame slot : Nat} {roots : Roots} {state : Partial.Locals} {guards : List Nat}
    (h : Frame world frame roots state guards) {r : Resources}
    (hr : Storage.inspectSlot world frame roots state slot = some r) : LocalResources world frame roots state slot r := by
  obtain ⟨actual, he, hv⟩ := h.inspectSlot slot
  have hh := Option.some.inj (he.symm.trans hr)
  cases hh
  exact hv

end Storage
end SubtreeProofs.Rust.LookupSource.Partial.Addressed

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed Storage

def drop (world : World) (active : Activation) (callers : List Activation) (slot : Nat) :
    Option (World × Activation) := do
  let item ← inspectSlot world active.frame active.roots active.state slot
  let (remainder, suspended) ← scanContext world active callers slot
  let binding ← active.roots slot
  let retained := remainder.reads ++ suspended.reads
  if item.owners.Nodup ∧ (∀ a ∈ item.owners, world.classes a = some .box) ∧
      binding.address ∉ retained ∧ (∀ a ∈ retained, a ∉ item.owners) then
    some (world.retire item.owners, { active with state := active.state.set slot .empty })
  else none

theorem drop_spec {world final : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed) {slot : Nat}
    (h : drop world active callers slot = some (final, after)) :
    Step world active callers (.drop slot) final after (Cost.local 1 (active.state slot).dropWork) ∧
      after.roots = active.roots ∧ after.state = active.state.set slot .empty ∧
      ∃ item binding, inspectSlot world active.frame active.roots active.state slot = some item ∧
        active.roots slot = some binding ∧ final = world.retire item.owners ∧ item.owners.Nodup ∧
        BoxOwners world item.owners ∧
        destroyLocal world.memory (rawAt world active.roots slot) (active.state slot) = some (item.owners, (active.state slot).dropWork) ∧
        item.owners.length = (active.state slot).dropWork.boxes ∧
        (∀ a ∈ item.owners, world.live a = true ∧ final.live a = false) ∧
        final.live binding.address = true := by
  unfold drop at h
  cases hi : inspectSlot world active.frame active.roots active.state slot with
  | none => simp [hi] at h
  | some item =>
    cases hctx : scanContext world active callers slot with
    | none => simp [hi, hctx] at h
    | some context =>
      rcases context with ⟨remainder, suspended⟩
      cases hb : active.roots slot with
      | none => simp [hi, hctx, hb] at h
      | some binding =>
        simp only [hi, hctx, hb, Bind.bind, Option.bind] at h
        split at h
        next ready =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨guards, hf⟩ := ha.2
          have hv := hf.inspectSlot_spec hi
          obtain ⟨context, hs, callers⟩ := scanContext_spec ha hc hctx
          obtain ⟨cell, used, hcell, hclass, _, hsub⟩ := hf.get hb
          have hroot : world.live binding.address = true := hf.alive _ (hsub (List.mem_append_right _ (by simp)))
          have hn : binding.address ∉ item.owners := BoxOwners.stack_disjoint ready.2.1 hclass
          have hl : (world.retire item.owners).live binding.address = true := by
            simpa only [World.retire, retire_other world.live hn] using hroot
          have hp := world.retire_keeps ready.2.2.2
          have kept := context.keep hp
          have rebound := kept.bind (slot := slot) (by simp [Roots.set]) (binding := binding)
            hcell hclass (PartialGraph.empty cell) (by
              intro a hm
              simpa only [List.nil_append, List.mem_singleton.mp hm] using hl)
          have hframe : Frame (world.retire item.owners) active.frame active.roots (active.state.set slot .empty)
              ((remainder.reads ++ suspended.reads) ++ [] ++ [binding.address]) := by
            simpa only [Roots.set_restore hb, locals_set_overwrite] using rebound.2
          refine ⟨⟨fun _ => rfl, rfl, rfl, ⟨ha.1, _, hframe⟩, hw.retire _,
              suspended, hs, callers.transport (hp.preserves.weaken (fun _ hm => List.mem_append_right _ hm))⟩,
            rfl, rfl, item, binding, rfl, rfl, rfl, ready.1, ready.2.1, hv.source.destroy, hv.boxes, ?_, hl⟩
          intro a hm
          exact ⟨hv.alive a (hv.owners_subset_reads hm), retire_member _ hm⟩
        next => cases h

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
