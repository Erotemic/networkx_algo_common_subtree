module

public import SubtreeProofs.Rust.SourceOwnerRetirement
public import SubtreeProofs.Rust.SourceActivationInitial

/-! Function entry moves the complete owned argument packet into the actual
parameter locals, allocating only symbolic stack storage. Shared argument and
caller read graphs may alias; their owner occurrences remain separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open Heap

theorem OwnerState.collect_get (items : List (List Nat)) (count : Nat) (bound : items.length ≤ count) :
    OwnerState.collect (fun slot => (items[slot]?).getD []) (List.range count) = items.flatten := by
  induction count generalizing items with
  | zero =>
    have he : items = [] := List.length_eq_zero_iff.mp (by omega)
    subst items
    rfl
  | succ count ih =>
    cases items with
    | nil => simp [OwnerState.collect]
    | cons first rest =>
      simp only [OwnerState.collect, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
        List.getElem?_cons_zero, Option.getD_some, List.getElem?_cons_succ, List.flatten_cons]
      exact congrArg (first ++ ·) (ih rest (by simp only [List.length_cons] at bound; omega))

namespace Storage

open SourceEval.Addressed

def packetOwners (world : World) (packets : List ValueCell) : List Nat :=
  packets.flatMap (fun p => ownerList world.memory (some p.1) (Slot.ofValue p.2))

theorem packetOwners_footprint {world : World} {packets : List ValueCell}
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2) :
    FieldsFootprint world.memory (packets.map Prod.fst) (packetOwners world packets) := by
  induction packets with
  | nil => exact .nil
  | cons packet rest ih =>
    obtain ⟨owners, ho, _⟩ := readable_owners (hp packet (by simp))
    obtain ⟨used, hg, _⟩ := hp packet (by simp)
    have hc := (LocalRep.stored (Rep.of_full hg.represents ho)).ownerList
    change FieldsFootprint world.memory (packet.1 :: rest.map Prod.fst)
      (ownerList world.memory (some packet.1) (Slot.ofValue packet.2) ++ packetOwners world rest)
    rw [hc]
    exact .cons ho (ih (fun p hm => hp p (List.mem_cons_of_mem _ hm)))

theorem packetOwners_unique {world : World} {packets : List ValueCell} {owners : List Nat}
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (ho : FieldsFootprint world.memory (packets.map Prod.fst) owners) : packetOwners world packets = owners :=
  (packetOwners_footprint hp).unique ho

theorem initialActivation_ownerState {world : World} (frame count : Nat) {packets : List ValueCell}
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2) :
    ownerState (world.stackCells frame (packets.map Prod.fst)).memory
      (rawAt (world.stackCells frame (packets.map Prod.fst)) (initialActivation world frame count packets).roots)
      (initialActivation world frame count packets).state =
      fun slot => (([] :: packets.map (fun p => ownerList world.memory (some p.1) (Slot.ofValue p.2)))[slot]?).getD [] := by
  funext slot
  cases slot with
  | zero =>
    simp only [ownerState, initialActivation, SourceEval.initialState, Partial.Locals.lift, initialEnv,
      ite_true, ownerList_empty, List.getElem?_cons_zero, Option.getD_some]
  | succ index =>
    by_cases hi : index < packets.length
    · let packet := packets[index]
      have hg : packets[index]? = some packet := List.getElem?_eq_getElem hi
      obtain ⟨used, graph, _⟩ := hp packet (List.mem_of_getElem? hg)
      obtain ⟨r, _, _, resources⟩ := graph.partial.resources
      have prior := (LocalRep.stored resources.owned).ownerList
      have later := (LocalRep.stored (resources.owned.mono (Extends.append world.memory (packets.map Prod.fst)))).ownerList
      have cell : (world.stackCells frame (packets.map Prod.fst)).memory[world.memory.length + index]? = some packet.1 := by
        change (world.memory ++ packets.map Prod.fst)[world.memory.length + index]? = some packet.1
        rw [List.getElem?_append_right (by omega)]
        simp only [Nat.add_sub_cancel_left, List.getElem?_map, hg, Option.map_some]
      have arg : 0 < index + 1 ∧ index + 1 ≤ packets.length := by omega
      simp only [ownerState, initialActivation, rawAt, argumentRoots, arg, and_self, ite_true, Nat.add_sub_cancel,
        cell, Bind.bind, Option.bind, SourceEval.initialState, Partial.Locals.lift, initialEnv,
        Nat.add_one_ne_zero, ite_false, List.getElem?_map, hg, Option.map_some,
        List.getElem?_cons_succ, Option.getD_some]
      exact later.trans prior.symm
    · have hnone : packets[index]? = none := List.getElem?_eq_none (by omega)
      have arg : ¬ (0 < index + 1 ∧ index + 1 ≤ packets.length) := by omega
      simp only [ownerState, initialActivation, rawAt, argumentRoots, arg, ite_false,
        Bind.bind, Option.bind, SourceEval.initialState, Partial.Locals.lift, initialEnv,
        Nat.add_one_ne_zero, Nat.add_sub_cancel, List.getElem?_map, hnone, Option.map_none,
        List.getElem?_cons_succ, Option.getD_none, ownerList_empty]

theorem initialActivation_owners {world : World} (frame count : Nat) {packets : List ValueCell}
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2) (bound : packets.length + 1 ≤ count) :
    (initialActivation world frame count packets).owners (world.stackCells frame (packets.map Prod.fst)) = packetOwners world packets := by
  unfold Activation.owners
  rw [initialActivation_ownerState frame count hp]
  dsimp only [initialActivation]
  rw [OwnerState.collect_get _ count (by simpa only [List.length_cons, List.length_map] using bound)]
  simp only [List.flatten_cons, List.nil_append, packetOwners, List.flatMap_def]

theorem OwnerFrame.keep {before after : World} {owners : List Nat} (h : OwnerFrame before owners)
    (hk : Keeps before after owners) : OwnerFrame after owners :=
  ⟨h.unique, fun a ha => hk.classes a .box (h.classified a ha), fun a ha => hk.alive a ha (h.alive a ha)⟩

theorem BoxCoverage.stackCells {world : World} {owners : List Nat} (h : BoxCoverage world owners)
    (frame : Nat) (cells : List Cell) : BoxCoverage (world.stackCells frame cells) owners := by
  intro a hc hl
  by_cases hb : a < world.memory.length
  · simp only [World.stackCells, hb, ite_true] at hc hl
    exact h a hc hl
  · simp only [World.stackCells, hb, ite_false] at hc
    split at hc <;> cases hc

theorem enter_owner_resources {world final : World} {entered : Activation} (hw : world.WellFormed)
    (frame count : Nat) {packets : List ValueCell} {callers : List Activation} {owners external : List Nat}
    (hc : ∀ a ∈ callers, a.Valid world)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (ho : FieldsFootprint world.memory (packets.map Prod.fst) owners)
    (hf : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (h : enter world frame count packets = some (final, entered)) :
    OwnerFrame final (entered.owners final ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (entered.owners final ++ (callerOwners final callers ++ external)) := by
  unfold enter at h
  split at h
  next ready =>
    cases h
    obtain ⟨r, _, callers⟩ := scanCallers_complete callers hc
    have kept := (world.stackCells_keeps hw frame (packets.map Prod.fst) r.reads).preserves
    have hs := callers.owners_preserved (callers.transport kept)
    rw [initialActivation_owners frame count hp ready.1, packetOwners_unique hp ho, ← hs]
    exact ⟨hf.keep (world.stackCells_keeps hw _ _ _), covered.stackCells _ _⟩
  next => cases h

end Storage
end SubtreeProofs.Rust.LookupSource.Partial.Addressed
