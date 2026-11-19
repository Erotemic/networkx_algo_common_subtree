module

public import SubtreeProofs.Rust.SourceBoxOrigin
public import SubtreeProofs.Rust.SourceOwnerActions

/-! Successful guarded stores, assignments and non-call source actions retain
backward live-Box provenance. These facts concern actual world transitions. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage

theorem store_boxOrigin {world final : World} {roots : Roots} {frame slot : Nat}
    {retained : List Nat} {middle after : State} {packet : ValueCell}
    (h : store world roots frame slot retained middle packet = some (final, after)) :
    BoxOrigin world final := by
  unfold store at h
  split at h
  next =>
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨binding, _, used, _, next, written, last⟩ := h
    cases last
    obtain ⟨_, _, _, _, rfl⟩ := World.writeStack_iff.mp written
    exact world.write_boxOrigin _ _
  next => cases h

theorem assign_boxOrigin {world final : World} {active after : Activation} {callers : List Activation}
    {slot : Nat} {rhs : Expr}
    (h : assign world active callers slot rhs = some (final, after)) : BoxOrigin world final := by
  simp only [assign, bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, ⟨_, _⟩, _, _, _, ⟨next, state⟩, stored, last⟩ := h
  cases last
  exact store_boxOrigin stored

theorem action_boxOrigin {world final : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (instruction : Action) (h : action world active callers instruction = some (final, after)) :
    BoxOrigin world final := by
  cases instruction with
  | storageLive slot =>
    change storageLive world active callers slot = some (final, after) at h
    unfold storageLive at h
    split at h
    next =>
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, _, _, _, last⟩ := h
      cases last
      exact world.allocate_boxOrigin _ _
    next => cases h
  | storageDead slot =>
    obtain ⟨_, _, _, _, _, _, he, _⟩ := storageDead_spec ha hc hw h
    rw [he]
    exact world.retire_boxOrigin _
  | drop slot =>
    obtain ⟨_, _, _, _, _, _, _, he, _⟩ := drop_spec ha hc hw h
    rw [he]
    exact world.retire_boxOrigin _
  | assign slot rhs => exact assign_boxOrigin h
  | fakeRead _ => cases h; exact .refl _
  | call _ _ _ | undefinedBehavior => cases h

def CallsBoxOrigin (callee : Callees) : Prop :=
  ∀ world guards callers function packets final packet cost,
    world.WellFormed → (∀ a ∈ callers, a.Valid world) →
    (∀ p ∈ packets, Readable world.memory world.live p.1 p.2) →
    TypedReady world function packets →
    callee world guards callers function packets = some (final, packet, cost) → BoxOrigin world final

theorem call_boxOrigin {callee : Callees} (origin : CallsBoxOrigin callee)
    {world final : World} {active after : Activation} {callers : List Activation} {cost : Cost}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world)
    (hw : world.WellFormed) (function : Function) (args : List Operand) (slot : Nat)
    (hd : ∀ current suspended packets masks, active.scan world = some current →
      scanCallers world callers = some suspended →
      operands world active.roots (current.loans ++ suspended.reads) active.state args = some (packets, masks) →
      TypedReady world function packets)
    (h : call callee world active callers function args slot = some (final, after, cost)) :
    BoxOrigin world final := by
  simp only [call, bind, Option.bind_eq_some_iff] at h
  obtain ⟨current, currentScan, suspended, callerScan, ⟨packets, masks⟩, arguments,
    remainder, _, binding, _, ⟨middle, packet, inner⟩, called, ⟨next, state⟩, stored, last⟩ := h
  cases last
  have frame := (Activation.scan_spec ha currentScan).frame
  obtain ⟨_, _, graph, subset, masksFrame⟩ := operands_spec frame args arguments
  have readable := packets_readable graph (fun a hm => frame.alive a (subset hm))
  have callersValid : ∀ a ∈ ({ active with state := masks } :: callers), a.Valid world := by
    intro a hm
    rcases List.mem_cons.mp hm with he | hm
    · subst a; exact ⟨ha.1, _, masksFrame⟩
    · exact hc a hm
  exact (origin world _ _ function packets middle packet inner hw callersValid readable
    (hd current suspended packets masks currentScan callerScan arguments) called).trans (store_boxOrigin stored)

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
