module

public import SubtreeProofs.Rust.SourceEvalCallingControl

/-! Return cleanup retires every remaining bounded stack binding, after checking
that no Box owners remain and that the complete returned/caller read graphs do
not reach those roots. Memory and Box liveness are unchanged. This is symbolic
stack closure, separate from dynamic parsed-region and exclusive-owner proofs. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open Heap SourceEval.Addressed

def Activation.stackAddresses (active : Activation) : List Nat :=
  (List.range active.count).filterMap fun slot => (active.roots slot).map Binding.address

theorem Activation.mem_stackAddresses {active : Activation} {address : Nat} :
    address ∈ active.stackAddresses ↔ ∃ slot binding, slot < active.count ∧
      active.roots slot = some binding ∧ binding.address = address := by
  simp only [stackAddresses, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨slot, hb, hm⟩
    cases hr : active.roots slot with
    | none => simp [hr] at hm
    | some binding => exact ⟨slot, binding, hb, hr, Option.some.inj (by simpa only [hr, Option.map_some] using hm)⟩
  · rintro ⟨slot, binding, hb, hr, rfl⟩
    exact ⟨slot, hb, by simp only [hr, Option.map_some]⟩

theorem Activation.binding_mem {active : Activation} {world : World} (ha : active.Valid world)
    {slot : Nat} {binding : Binding} (hr : active.roots slot = some binding) : binding.address ∈ active.stackAddresses := by
  apply mem_stackAddresses.mpr
  refine ⟨slot, binding, ?_, hr, rfl⟩
  by_contra hn
  have hh := ha.1 slot (by omega)
  rw [hr] at hh
  cases hh

theorem Activation.stack_class {active : Activation} {world : World} (ha : active.Valid world)
    {address : Nat} (hm : address ∈ active.stackAddresses) :
    ∃ slot generation, world.classes address = some (.stack active.frame slot generation) ∧ world.live address = true := by
  obtain ⟨slot, binding, _, hr, rfl⟩ := mem_stackAddresses.mp hm
  obtain ⟨guards, hf⟩ := ha.2
  obtain ⟨_, _, _, hc, _, hs⟩ := hf.get hr
  exact ⟨slot, binding.generation, hc, hf.alive _ (hs (List.mem_append_right _ (by simp)))⟩

theorem Scanned.zero_boxes {world : World} {active : Activation} {r : Resources}
    (h : Scanned world active r) (hz : r.owners = []) (slot : Nat) : (active.state slot).dropWork.boxes = 0 := by
  by_cases hb : slot < active.count
  · obtain ⟨item, hi, _, ho, _⟩ := h.inventory.get (List.mem_range.mpr hb)
    have he : item.owners = [] := List.eq_nil_iff_forall_not_mem.mpr (by
      intro a hm
      have hh := ho hm
      rw [hz] at hh
      cases hh)
    have hh := hi.boxes
    simpa only [he, List.length_nil] using hh.symm
  · have he := h.bounded slot (by omega)
    have hs := h.frame.slots slot
    have hempty : active.state slot = .empty := by simpa only [he] using hs
    simp only [hempty, Slot.dropWork]

def close (world : World) (active : Activation) (callers : List Activation) (guards : List Nat) (packet : ValueCell) :
    Option World := do
  let current ← active.scan world
  let suspended ← scanCallers world callers
  let used ← traceGraph world.memory packet.1 packet.2
  if current.owners = [] ∧ used.all world.live ∧
      active.stackAddresses.all (fun address => decide (address ∉ guards ++ suspended.reads ++ used)) then
    some (world.retire active.stackAddresses)
  else none

theorem close_spec {world final : World} {active : Activation} {callers : List Activation} {guards : List Nat} {packet : ValueCell}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (hp : Readable world.memory world.live packet.1 packet.2)
    (h : close world active callers guards packet = some final) :
    final = world.retire active.stackAddresses ∧ final.memory = world.memory ∧ final.classes = world.classes ∧
      final.WellFormed ∧ Readable final.memory final.live packet.1 packet.2 ∧ Preserves world final guards ∧
      (∀ slot, (active.state slot).dropWork.boxes = 0) ∧
      (∀ slot binding, active.roots slot = some binding → final.live binding.address = false) ∧
      (∀ address, world.classes address = some .box → final.live address = world.live address) ∧
      ∃ suspended, scanCallers world callers = some suspended ∧ Callers final callers suspended ∧
        Preserves world final suspended.reads := by
  unfold close at h
  cases hs : active.scan world with
  | none => simp [hs] at h
  | some current =>
    cases hcScan : scanCallers world callers with
    | none => simp [hs, hcScan] at h
    | some suspended =>
      cases ht : traceGraph world.memory packet.1 packet.2 with
      | none => simp [hs, hcScan, ht] at h
      | some used =>
        simp only [hs, hcScan, ht, Bind.bind, Option.bind] at h
        split at h
        next accepted =>
          obtain ⟨hz, hl, hsep⟩ := accepted
          have disjoint : ∀ a ∈ guards ++ suspended.reads ++ used, a ∉ active.stackAddresses := by
            intro a hm hb
            have hh := List.all_eq_true.mp hsep a hb
            exact of_decide_eq_true hh hm
          obtain rfl := Option.some.inj h
          have kept := (world.retire_keeps disjoint).preserves
          have packetKept := kept.weaken (fun _ hm => List.mem_append_right _ hm)
          have callerKept := kept.weaken (fun _ hm => List.mem_append_left _ (List.mem_append_right _ hm))
          obtain ⟨known, graph, _⟩ := hp
          have he := Option.some.inj (ht.symm.trans graph.trace)
          subst known
          refine ⟨rfl, rfl, rfl, hw.retire _, ?_, ?_, (Activation.scan_spec ha hs).zero_boxes hz, ?_, ?_,
            suspended, rfl, (scanCallers_spec hc hcScan).transport callerKept, callerKept⟩
          · exact ⟨used, graph, fun a hm => packetKept.alive a hm (List.all_eq_true.mp hl a hm)⟩
          · exact kept.weaken (fun _ hm => List.mem_append_left _ (List.mem_append_left _ hm))
          · intro slot binding hr
            exact retire_member _ (active.binding_mem ha hr)
          · intro address hbox
            apply retire_other
            intro hm
            obtain ⟨slot, generation, ht, _⟩ := active.stack_class ha hm
            cases hbox.symm.trans ht
        next => cases h

theorem close_complete {world : World} {active : Activation} {callers : List Activation} {guards : List Nat} {packet : ValueCell}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world)
    (hz : ∀ current, active.scan world = some current → current.owners = [])
    (hp : Readable world.memory world.live packet.1 packet.2)
    (hsep : ∀ suspended used, scanCallers world callers = some suspended →
      Graph world.memory packet.1 packet.2 used → ∀ address ∈ active.stackAddresses,
        address ∉ guards ++ suspended.reads ++ used) :
    close world active callers guards packet = some (world.retire active.stackAddresses) := by
  obtain ⟨current, hs, _⟩ := active.scan_complete ha
  obtain ⟨suspended, hcScan, _⟩ := scanCallers_complete callers hc
  obtain ⟨used, hg, hl⟩ := hp
  have hall : active.stackAddresses.all (fun address => decide (address ∉ guards ++ suspended.reads ++ used)) = true :=
    List.all_eq_true.mpr (fun a hm => decide_eq_true (hsep suspended used hcScan hg a hm))
  simp only [close, hs, hcScan, hg.trace, Bind.bind, Option.bind, hz current hs, List.all_eq_true.mpr hl, hall,
    and_self, ite_true]

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage
