module

public import SubtreeProofs.Rust.SourceOwnerEntry

/-! Actual storage-live/dead operations conserve complete Box ownership.
Initialized nonowning locals may end storage after the existing read guards
pass. New symbolic stack roots never enter the Box owner ledger. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open Heap

theorem Activation.bind_empty_owners (active : Activation) (world : World) (slot : Nat) (binding : Option Binding)
    (he : active.state slot = .empty) :
    ({active with roots := active.roots.set slot binding, state := active.state.set slot .empty} : Activation).owners world =
      active.owners world := by
  apply congrArg (fun owners : OwnerState => owners.collect (List.range active.count))
  funext index
  by_cases hs : index = slot
  · subst index
    simp only [ownerState, Partial.Locals.set, ite_true, he, ownerList_empty]
  · simp only [ownerState, rawAt, Roots.set, Partial.Locals.set, hs, ite_false]

theorem Activation.withoutLocal_zero_owners (active : Activation) (world : World) (slot : Nat)
    (he : ownerState world.memory (rawAt world active.roots) active.state slot = []) :
    (active.withoutLocal slot).owners world = active.owners world := by
  change (ownerState world.memory (rawAt world (active.withoutLocal slot).roots) (active.withoutLocal slot).state).collect
    (List.range active.count) = _
  rw [Activation.withoutLocal_ownerState]
  apply congrArg (fun owners : OwnerState => owners.collect (List.range active.count))
  funext index
  by_cases hs : index = slot
  · subst index
    simp only [OwnerState.set, ite_true, he]
  · simp only [OwnerState.set, hs, ite_false]

theorem OwnerFrame.retire_stack {world : World} {owners : List Nat} (h : OwnerFrame world owners)
    {address frame slot generation : Nat} (hc : world.classes address = some (.stack frame slot generation)) :
    OwnerFrame (world.retire [address]) owners := by
  refine ⟨h.unique, h.classified, ?_⟩
  intro a ha
  have hn : a ∉ [address] := by
    intro hm
    have he := List.mem_singleton.mp hm
    exact h.classified.stack_disjoint hc (he ▸ ha)
  simpa only [World.retire, retire_other world.live hn] using h.alive a ha

theorem BoxCoverage.retire_same {world : World} {owners : List Nat} (h : BoxCoverage world owners)
    (discarded : List Nat) : BoxCoverage (world.retire discarded) owners := by
  intro a hc hl
  by_cases hm : a ∈ discarded
  · simp only [World.retire, retire_member world.live hm] at hl
    cases hl
  · exact h a hc (by simpa only [World.retire, retire_other world.live hm] using hl)

theorem BoxCoverage.allocate_stack {world : World} {owners : List Nat} (h : BoxCoverage world owners)
    (frame slot generation : Nat) (cell : Cell) : BoxCoverage (world.allocate (.stack frame slot generation) cell) owners := by
  intro a hc hl
  by_cases he : a = world.memory.length
  · simp only [World.allocate, he, ite_true] at hc
    cases hc
  · simp only [World.allocate, he, ite_false] at hc hl
    exact h a hc hl

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage

theorem storageLive_owner_resources {world final : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed) {slot : Nat}
    {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    (h : storageLive world active callers slot = some (final, after)) :
    after.owners final = active.owners world ∧ callerOwners final callers = callerOwners world callers ∧
      OwnerFrame final (after.owners final ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (after.owners final ++ (callerOwners final callers ++ external)) := by
  have step := storageLive_spec ha hc hw h
  unfold storageLive at h
  split at h
  next ready =>
    cases hr : active.scan world with
    | none => simp [hr] at h
    | some r =>
      cases hs : scanCallers world callers with
      | none => simp [hr, hs] at h
      | some suspended =>
        simp only [hr, hs, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨guards, frame⟩ := ha.2
        have he : active.state slot = .empty := by simpa only [ready.2] using frame.slots slot
        have hk := world.allocate_keeps hw (.stack active.frame slot world.memory.length) (.node .tuple 0 []) guards
        have kept := frame.ownerState_preserve hk.preserves
        have owners : active.owners (world.allocate (.stack active.frame slot world.memory.length) (.node .tuple 0 [])) = active.owners world :=
          congrArg (fun owners : OwnerState => owners.collect (List.range active.count)) kept
        have afterOwners := active.bind_empty_owners
          (world.allocate (.stack active.frame slot world.memory.length) (.node .tuple 0 [])) slot
          (some ⟨world.memory.length, world.memory.length⟩) he
        rw [owners] at afterOwners
        obtain ⟨r, hs, hpost, _⟩ := step.suspended
        have callers := (scanCallers_spec hc hs).owners_preserved hpost
        refine ⟨afterOwners, callers.symm, ?_⟩
        rw [afterOwners, ← callers]
        exact ⟨hf.keep (world.allocate_keeps hw _ _ _), covered.allocate_stack _ _ _ _⟩
  next => cases h

theorem storageDead_owner_resources {world final : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed) {slot : Nat}
    {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    (h : storageDead world active callers slot = some (final, after)) :
    after.owners final = active.owners world ∧ callerOwners final callers = callerOwners world callers ∧
      OwnerFrame final (after.owners final ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (after.owners final ++ (callerOwners final callers ++ external)) := by
  obtain ⟨step, hroots, hstate, zero, binding, hb, hfinal, _⟩ := storageDead_spec ha hc hw h
  obtain ⟨_, frame⟩ := ha.2
  have hz : ownerState world.memory (rawAt world active.roots) active.state slot = [] := by
    apply List.length_eq_zero_iff.mp
    exact (frame.ownerState slot).boxes.trans zero
  obtain ⟨_, _, _, hclass, _, _⟩ := frame.get hb
  have he : after = active.withoutLocal slot := by
    cases active
    cases after
    simp only [Activation.withoutLocal, Activation.mk.injEq]
    exact ⟨step.frame, step.count, hroots, hstate⟩
  have owners : after.owners final = active.owners world := by
    rw [he, hfinal, Activation.owners_retire, Activation.withoutLocal_zero_owners _ _ _ hz]
  obtain ⟨r, hs, hpost, _⟩ := step.suspended
  have callers := (scanCallers_spec hc hs).owners_preserved hpost
  refine ⟨owners, callers.symm, ?_⟩
  rw [owners, ← callers, hfinal]
  exact ⟨hf.retire_stack hclass, covered.retire_same _⟩

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
