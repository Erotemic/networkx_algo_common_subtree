module

public import SubtreeProofs.Rust.SourceOwnerEntry
public import SubtreeProofs.Rust.SourceOwnerCallees

/-! Backward provenance of live Box identities. Memory may grow and cells may
be written or retired, but an old live Box cannot arise from a dead cell or a
stack identity. Together with complete ownership this derives fresh output
owners for ownership-free inputs; shared reads may still alias old owners. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open Heap SourceEval.Addressed

structure BoxOrigin (before after : World) : Prop where
  length : before.memory.length ≤ after.memory.length
  old : ∀ address, address < before.memory.length →
    after.classes address = some .box → after.live address = true →
    before.classes address = some .box ∧ before.live address = true

theorem BoxOrigin.refl (world : World) : BoxOrigin world world :=
  ⟨Nat.le_refl _, fun _ _ hc hl => ⟨hc, hl⟩⟩

theorem BoxOrigin.trans {first second third : World}
    (h₁ : BoxOrigin first second) (h₂ : BoxOrigin second third) : BoxOrigin first third := by
  refine ⟨h₁.length.trans h₂.length, ?_⟩
  intro a hb hc hl
  obtain ⟨hc, hl⟩ := h₂.old a (by have := h₁.length; omega) hc hl
  exact h₁.old a hb hc hl

theorem World.allocate_boxOrigin (world : World) (kind : Class) (cell : Cell) :
    BoxOrigin world (world.allocate kind cell) := by
  refine ⟨by simp [World.allocate], ?_⟩
  intro a hb hc hl
  have hn : a ≠ world.memory.length := by omega
  simpa only [World.allocate, hn, ite_false] using And.intro hc hl

theorem World.retire_boxOrigin (world : World) (discarded : List Nat) :
    BoxOrigin world (world.retire discarded) := by
  refine ⟨Nat.le_refl _, ?_⟩
  intro a _ hc hl
  by_cases hm : a ∈ discarded
  · simp only [World.retire, retire_member world.live hm] at hl
    cases hl
  · exact ⟨hc, by simpa only [World.retire, retire_other world.live hm] using hl⟩

theorem World.write_boxOrigin (world : World) (address : Nat) (cell : Cell) :
    BoxOrigin world (world.write address cell) :=
  ⟨by simp [World.write], fun _ _ hc hl => ⟨hc, hl⟩⟩

theorem World.boxSuffix_boxOrigin (world : World) {memory : Memory}
    (he : Extends world.memory memory) : BoxOrigin world (world.boxSuffix memory) := by
  refine ⟨he.length_le, ?_⟩
  intro a hb hc hl
  simpa only [World.boxSuffix, hb, ite_true] using And.intro hc hl

theorem World.stackCells_boxOrigin (world : World) (frame : Nat) (cells : List Cell) :
    BoxOrigin world (world.stackCells frame cells) := by
  refine ⟨by simp [World.stackCells], ?_⟩
  intro a hb hc hl
  simpa only [World.stackCells, hb, ite_true] using And.intro hc hl

theorem BoxOrigin.of_maps {before after : World} (hb : before.WellFormed) (ha : after.WellFormed)
    (hc : after.classes = before.classes) (hl : after.live = before.live) : BoxOrigin before after := by
  refine ⟨?_, fun _ _ hclass halive => ⟨hc ▸ hclass, hl ▸ halive⟩⟩
  by_contra hn
  have bound : after.memory.length < before.memory.length := by omega
  have present := (hb.1 after.memory.length).mpr bound
  rw [← hc] at present
  have := (ha.1 after.memory.length).mp present
  omega

theorem BoxOrigin.fresh_output {before after : World} {output retained : List Nat}
    (h : BoxOrigin before after) (covered : BoxCoverage before retained)
    (frame : OwnerFrame after (output ++ retained)) :
    ∀ address ∈ output, before.memory.length ≤ address := by
  intro a hm
  by_contra hn
  have member := List.mem_append_left retained hm
  obtain ⟨hc, hl⟩ := h.old a (by omega) (frame.classified a member) (frame.alive a member)
  exact List.disjoint_left.mp frame.unique.disjoint hm (covered a hc hl)

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

namespace SubtreeProofs.Rust.SourceEval.Addressed.Helpers

open LookupSource Heap Partial Partial.Addressed Storage

theorem callee_boxOrigin (fuel budget : Nat) {world final : World} (hw : world.WellFormed)
    (function : Function) (packets : List ValueCell)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (typed : Derived.TypedReady world function packets)
    {guards : List Nat} {callers : List Activation} {packet : ValueCell} {cost : Cost}
    (h : callee fuel budget world guards callers function packets = some (final, packet, cost)) :
    BoxOrigin world final := by
  obtain ⟨_, _, _, he, shape⟩ := callee_owner_ledger fuel budget hw function packets hp typed
    (packetOwners_footprint hp) h
  conv_rhs => rw [shape]
  exact world.boxSuffix_boxOrigin he

end SubtreeProofs.Rust.SourceEval.Addressed.Helpers
