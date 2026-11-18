module

public import SubtreeProofs.Rust.SourceEvalDerivedAssignments
public import SubtreeProofs.Rust.SourceEvalFrameActions

/-! Storage markers derive retained contexts from the actual bounded activation
and caller stack. Ending initialized nonowning storage protects its stack root,
even when its Box-owner inventory is empty. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

theorem Bounded.set_none {roots : Roots} {count : Nat} (h : Bounded roots count) (slot : Nat) :
    Bounded (roots.set slot none) count := by
  intro index hi
  by_cases hs : index = slot <;> simp only [Roots.set, hs, ite_true, ite_false, h index hi]

theorem Bounded.set_some {roots : Roots} {count slot : Nat} (h : Bounded roots count)
    (hs : slot < count) (binding : Binding) : Bounded (roots.set slot (some binding)) count := by
  intro index hi
  have hn : index ≠ slot := by omega
  simp only [Roots.set, hn, ite_false, h index hi]

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed Storage

/-- These are complete remaining active reads and all suspended caller reads. -/
def scanContext (world : World) (active : Activation) (callers : List Activation) (slot : Nat) :
    Option (Resources × Resources) := do
  let remainder ← active.scanExcept world slot
  let suspended ← scanCallers world callers
  some (remainder, suspended)

theorem scanContext_spec {world : World} {active : Activation} {callers : List Activation} {slot : Nat}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) {remainder suspended : Resources}
    (h : scanContext world active callers slot = some (remainder, suspended)) :
    Frame world active.frame (active.roots.set slot none) (active.state.set slot .empty)
      (remainder.reads ++ suspended.reads) ∧
      scanCallers world callers = some suspended ∧ Callers world callers suspended := by
  unfold scanContext at h
  cases hr : active.scanExcept world slot with
  | none => simp [hr] at h
  | some r =>
    cases hs : scanCallers world callers with
    | none => simp [hr, hs] at h
    | some s =>
      simp only [hr, hs, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hf := Activation.context_spec ha slot hr
      have callers := scanCallers_spec hc hs
      refine ⟨hf.weaken (fun _ hm => List.mem_append_left _ hm) ?_, rfl, callers⟩
      intro a hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hf.alive a hm
      · exact callers.alive a hm

/-- Common result for these non-call actions; the caller interpreter is arbitrary. -/
structure Step (world : World) (active : Activation) (callers : List Activation)
    (instruction : Action) (final : World) (after : Activation) (cost : Cost) : Prop where
  source : ∀ call, SourceEval.action call active.state instruction = some (after.state, cost)
  frame : after.frame = active.frame
  count : after.count = active.count
  valid : after.Valid final
  wellFormed : final.WellFormed
  suspended : ∃ r, scanCallers world callers = some r ∧ Callers final callers r ∧ Preserves world final r.reads

theorem Step.callers {world final : World} {active after : Activation} {callers : List Activation}
    {instruction : Action} {cost : Cost} (h : Step world active callers instruction final after cost) :
    ∀ a ∈ callers, a.Valid final := by
  obtain ⟨_, _, hc, _⟩ := h.suspended
  intro a hm
  obtain ⟨_, hs, _, _, _⟩ := hc.get hm
  exact hs.valid

def storageLive (world : World) (active : Activation) (callers : List Activation) (slot : Nat) :
    Option (World × Activation) := do
  if slot < active.count ∧ active.roots slot = none then
    let _ ← active.scan world
    let _ ← scanCallers world callers
    let address := world.memory.length
    some (world.allocate (.stack active.frame slot address) (.node .tuple 0 []),
      { active with roots := active.roots.set slot (some ⟨address, address⟩), state := active.state.set slot .empty })
  else none

theorem storageLive_spec {world final : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed) {slot : Nat}
    (h : storageLive world active callers slot = some (final, after)) :
    Step world active callers (.storageLive slot) final after (Cost.local 1) := by
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
        have current := Activation.scan_spec ha hr
        have callers := scanCallers_spec hc hs
        have hf := AddressedPrimitives.action_storageLive current.frame hw (fun _ _ => none) slot world.memory.length ready.2
        exact ⟨fun _ => rfl, rfl, rfl, ⟨ha.1.set_some ready.1 _, _, hf.2.1⟩, hf.2.2,
          suspended, hs, callers.transport (world.allocate_keeps hw _ _ _).preserves,
          (world.allocate_keeps hw _ _ _).preserves⟩
  next => cases h

def storageDead (world : World) (active : Activation) (callers : List Activation) (slot : Nat) :
    Option (World × Activation) := do
  if (active.state slot).dropWork.boxes = 0 then
    let (remainder, suspended) ← scanContext world active callers slot
    let binding ← active.roots slot
    let final ← world.endStack active.frame slot binding (remainder.reads ++ suspended.reads)
    some (final, { active with roots := active.roots.set slot none, state := active.state.set slot .empty })
  else none

theorem storageDead_spec {world final : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed) {slot : Nat}
    (h : storageDead world active callers slot = some (final, after)) :
    Step world active callers (.storageDead slot) final after (Cost.local 1) ∧
      after.roots = active.roots.set slot none ∧ after.state = active.state.set slot .empty ∧
      (active.state slot).dropWork.boxes = 0 ∧
      ∃ binding, active.roots slot = some binding ∧ final = world.retire [binding.address] ∧
        final.live binding.address = false := by
  unfold storageDead at h
  split at h
  next zero =>
    cases hctx : scanContext world active callers slot with
    | none => simp [hctx] at h
    | some context =>
      rcases context with ⟨remainder, suspended⟩
      cases hb : active.roots slot with
      | none => simp [hctx, hb] at h
      | some binding =>
        simp only [hctx, hb, Bind.bind, Option.bind] at h
        unfold World.endStack at h
        by_cases ready : world.classes binding.address = some (.stack active.frame slot binding.generation) ∧
            world.live binding.address = true ∧ binding.address < world.memory.length ∧
            binding.address ∉ remainder.reads ++ suspended.reads
        · simp only [ite_eq_left ready, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨context, hs, callers⟩ := scanContext_spec ha hc hctx
          have hf := context.endStorage ready.2.2.2
          have hp := world.retire_keeps (guards := suspended.reads) (discarded := [binding.address]) (by
            intro a hm he
            exact ready.2.2.2 (List.mem_append_right _ (List.mem_singleton.mp he ▸ hm)))
          refine ⟨⟨fun _ => rfl, rfl, rfl, ⟨ha.1.set_none _, _, hf⟩, hw.retire _,
            suspended, hs, callers.transport hp.preserves, hp.preserves⟩, rfl, rfl, zero, binding, rfl, rfl, ?_⟩
          exact retire_member _ (by simp)
        · simp only [ite_eq_right ready] at h
          cases h
  next => cases h

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
