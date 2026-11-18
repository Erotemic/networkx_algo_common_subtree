module

public import SubtreeProofs.Rust.SourceOwnerCalls
public import SubtreeProofs.Rust.SourceActivationClose

/-! Return packets extract actual owners, and successful stack closure retains
that output/caller ownership and complete live-Box coverage. This is conditional
transfer through existing execution/cleanup, not universal physical success. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open Heap SourceEval.Addressed

theorem Activation.owners_zero {world : World} {active : Activation} (ha : active.Valid world)
    (hz : ∀ slot, (active.state slot).dropWork.boxes = 0) : active.owners world = [] := by
  obtain ⟨_, guards, hf⟩ := ha
  have hlocal (slot : Nat) : ownerState world.memory (rawAt world active.roots) active.state slot = [] := by
    apply List.length_eq_zero_iff.mp
    exact (hf.ownerState slot).boxes.trans (hz slot)
  have he : ownerState world.memory (rawAt world active.roots) active.state = fun _ => [] := funext hlocal
  simp only [Activation.owners, he, OwnerState.collect]
  exact List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)

theorem close_owner_transfer {world final : World} {active : Activation} {callers : List Activation}
    {guards owners external : List Nat} {packet : ValueCell}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (hp : Readable world.memory world.live packet.1 packet.2) (ho : Footprint world.memory packet.1 owners)
    (hf : OwnerFrame world (owners ++ (active.owners world ++ (callerOwners world callers ++ external))))
    (covered : BoxCoverage world (owners ++ (active.owners world ++ (callerOwners world callers ++ external))))
    (h : close world active callers guards packet = some final) :
    Footprint final.memory packet.1 owners ∧
      OwnerFrame final (owners ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (owners ++ (callerOwners final callers ++ external)) := by
  obtain ⟨_, hmemory, hclasses, _, _, _, hz, _, hboxes, suspended, hs, hcallers, _⟩ := close_spec ha hc hw hp h
  have hempty := Activation.owners_zero ha hz
  rw [hempty, List.nil_append] at hf covered
  have kept := (scanCallers_spec hc hs).owners_preserved hcallers
  rw [← kept]
  refine ⟨by simpa only [hmemory] using ho, ?_, ?_⟩
  · exact ⟨hf.unique, fun a hm => by rw [hclasses]; exact hf.classified a hm,
      fun a hm => by rw [hboxes a (hf.classified a hm)]; exact hf.alive a hm⟩
  · intro a hclass halive
    rw [hclasses] at hclass
    rw [hboxes a hclass] at halive
    exact covered a hclass halive

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap LookupSource.Partial LookupSource.Partial.Addressed Storage

theorem returnValue_owner_frame {world : World} {active : Activation} {callers : List Activation}
    {result : Flow} {cost : Cost} {external : List Nat} (ha : active.Valid world)
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (h : returnValue callers world active = some (result, cost)) :
    ∃ after packet owners, result = .returned world after packet ∧
      Footprint world.memory packet.1 owners ∧
      OwnerFrame world (owners ++ (after.owners world ++ (callerOwners world callers ++ external))) ∧
      (active.owners world).Perm (owners ++ after.owners world) := by
  unfold returnValue at h
  cases hs : active.scan world with
  | none => simp [hs] at h
  | some current =>
    cases hc : scanCallers world callers with
    | none => simp [hs, hc] at h
    | some suspended =>
      cases hm : Addressed.operand world active.roots (current.loans ++ suspended.reads) active.state (.move (.local 0)) with
      | none => simp [hs, hc, hm] at h
      | some pair =>
        rcases pair with ⟨packet, masks⟩
        simp only [hs, hc, hm, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨owners, ho, hp⟩ := operand_owners ha hm
        refine ⟨{ active with state := masks }, packet, owners, rfl, ho, ?_, hp⟩
        exact hf.perm (by simpa only [List.append_assoc] using hp.append_right (callerOwners world callers ++ external))

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
