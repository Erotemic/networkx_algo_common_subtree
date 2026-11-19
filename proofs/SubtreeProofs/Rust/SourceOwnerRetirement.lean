module

public import SubtreeProofs.Rust.SourceOwnerReturns

/-! Exact complete owner retirement through actual successful drops. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open Heap

theorem OwnerFrame.retire {world : World} {discarded retained : List Nat}
    (h : OwnerFrame world (discarded ++ retained)) : OwnerFrame (world.retire discarded) retained := by
  refine ⟨h.unique.of_append_right, fun a ha => h.classified a (List.mem_append_right _ ha), ?_⟩
  intro a ha
  have hn : a ∉ discarded := fun hd => List.disjoint_left.mp h.unique.disjoint hd ha
  simpa only [World.retire, retire_other world.live hn] using h.alive a (List.mem_append_right _ ha)

theorem BoxCoverage.retire {world : World} {discarded retained : List Nat}
    (h : BoxCoverage world (discarded ++ retained)) : BoxCoverage (world.retire discarded) retained := by
  intro a hc hl
  have hn : a ∉ discarded := by
    intro hd
    simp only [World.retire, retire_member world.live hd] at hl
    cases hl
  have old : world.live a = true := by simpa only [World.retire, retire_other world.live hn] using hl
  exact (List.mem_append.mp (h a hc old)).resolve_left hn

theorem Activation.owners_retire (active : Activation) (world : World) (discarded : List Nat) :
    active.owners (world.retire discarded) = active.owners world := rfl

theorem Activation.clear_owners (active : Activation) (world : World) (slot : Nat) :
    ({active with state := active.state.set slot .empty} : Activation).owners world = (active.withoutLocal slot).owners world := by
  rw [← Activation.withoutLocal_empty_owners ({active with state := active.state.set slot .empty} : Activation) world slot (by simp [Partial.Locals.set])]
  rw [Activation.withoutLocal_set]

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage

theorem drop_owner_partition {world final : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed) {slot : Nat}
    (h : drop world active callers slot = some (final, after)) :
    ∃ discarded, final = world.retire discarded ∧
      (active.owners world).Perm (discarded ++ after.owners final) ∧
      discarded.length = (active.state slot).dropWork.boxes ∧
      callerOwners final callers = callerOwners world callers := by
  obtain ⟨step, hroots, hstate, item, binding, hi, hb, hfinal, _, _, _, hlength, _, _⟩ := drop_spec ha hc hw h
  have bound : slot < active.count := by
    by_contra hn
    have hh := ha.1 slot (by omega)
    rw [hb] at hh
    cases hh
  obtain ⟨_, frame⟩ := ha.2
  have itemRep := frame.inspectSlot_spec hi
  have partition := active.owners_partition world slot bound itemRep.source.ownerList
  have he : after = {active with state := active.state.set slot .empty} := by
    cases active
    cases after
    simp only [Activation.mk.injEq]
    exact ⟨step.frame, step.count, hroots, hstate⟩
  rw [he, hfinal, Activation.owners_retire, Activation.clear_owners]
  obtain ⟨r, hs, hpost, _⟩ := step.suspended
  have callers := (scanCallers_spec hc hs).owners_preserved hpost
  exact ⟨item.owners, rfl, partition, hlength, by simpa only [hfinal] using callers.symm⟩

theorem drop_owner_resources {world final : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed) {slot : Nat}
    {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    (h : drop world active callers slot = some (final, after)) :
    ∃ discarded, final = world.retire discarded ∧ discarded.length = (active.state slot).dropWork.boxes ∧
      (active.owners world).Perm (discarded ++ after.owners final) ∧
      OwnerFrame final (after.owners final ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (after.owners final ++ (callerOwners final callers ++ external)) := by
  obtain ⟨discarded, he, hp, hl, hc⟩ := drop_owner_partition ha hc hw h
  have partition : (active.owners world ++ (callerOwners world callers ++ external)).Perm
      (discarded ++ (after.owners final ++ (callerOwners world callers ++ external))) := by
    simpa only [List.append_assoc] using hp.append_right (callerOwners world callers ++ external)
  have frame := (hf.perm partition).retire
  have coverage := (covered.perm partition).retire
  rw [← he, ← hc] at frame coverage
  exact ⟨discarded, he, hl, hp, frame, coverage⟩

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
