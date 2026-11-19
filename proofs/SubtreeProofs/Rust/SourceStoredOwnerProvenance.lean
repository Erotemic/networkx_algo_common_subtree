module

public import SubtreeProofs.Rust.SourceStoreTotality

/-! A guarded destination store retains the packet's exact Box-owner list.
Owner provenance concerns initialized descendants, independently of stack-root
freshness and of unrelated shared aliases elsewhere in the activation. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

def LocalOwnersAbove (bound : Nat) (world : World) (active : Activation) (slot : Nat) : Prop :=
  ∀ resources, LocalResources world active.frame active.roots active.state slot resources →
    ∀ address ∈ resources.owners, bound ≤ address

theorem LocalOwnersAbove.weaken {bound lower : Nat} {world : World} {active : Activation} {slot : Nat}
    (h : LocalOwnersAbove bound world active slot) (le : lower ≤ bound) : LocalOwnersAbove lower world active slot :=
  fun resources represented address member => le.trans (h resources represented address member)

theorem LocalOwnersAbove.of_zero {bound : Nat} {world : World} {active : Activation} {slot : Nat}
    (zero : (active.state slot).dropWork.boxes = 0) : LocalOwnersAbove bound world active slot := by
  intro resources represented address member
  have empty : resources.owners = [] := List.length_eq_zero_iff.mp (represented.boxes.trans zero)
  rw [empty] at member
  cases member

namespace Derived

theorem store_local_owners {world final : World} {roots : Roots} {frame slot : Nat} {retained : List Nat}
    {masks after : State} {packet : ValueCell} {owners : List Nat}
    (readable : Readable world.memory world.live packet.1 packet.2)
    (footprint : Footprint world.memory packet.1 owners)
    (run : store world roots frame slot retained masks packet = some (final, after)) :
    ∀ resources, LocalResources final frame roots after slot resources → resources.owners = owners := by
  rcases packet with ⟨cell, value⟩
  obtain ⟨used, graph, _⟩ := readable
  unfold store at run
  by_cases empty : emptySlot (masks slot) = true
  · cases root : roots slot with
    | none => simp [empty, root] at run
    | some binding =>
      cases written : world.writeStack frame slot binding (retained ++ used) cell with
      | none => simp [empty, root, graph.trace, written] at run
      | some next =>
        simp only [empty, root, graph.trace, written, bind, Option.bind, ite_true, Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        obtain ⟨_, _, bounded, separated, rfl⟩ := World.writeStack_iff.mp written
        have kept := world.write_preserves separated cell
        have transferred := graph.partial.owner_transport (Rep.of_full graph.represents footprint)
          (kept.reads.weaken (fun _ member => List.mem_append_right _ member))
        have localRep : LocalRep (world.write binding.address cell).memory
            (rawAt (world.write binding.address cell) roots slot)
            ((masks.set slot (Slot.ofValue value)) slot) owners := by
          simpa only [rawAt, root, (world.write_spec bounded cell).1, Partial.Locals.set, ite_true, bind, Option.bind]
            using LocalRep.stored transferred
        intro resources represented
        exact represented.source.ownerList.symm.trans localRep.ownerList
  · simp [empty] at run

end Derived
end SubtreeProofs.Rust.SourceEval.Addressed
