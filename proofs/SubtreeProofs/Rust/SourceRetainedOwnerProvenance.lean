module

public import SubtreeProofs.Rust.SourceExpressionOwnerProvenance
public import SubtreeProofs.Rust.SourceOriginalOwnedDrop
public import SubtreeProofs.Rust.SourceQueryCallPreservation
public import SubtreeProofs.Rust.SourceRawMaskPreservation

/-! Selected owner bounds survive actual unrelated storage, assignments and
drops. Real retained inventories supply the preservation facts; no post-frame
or desired successful surrounding invocation is supplied. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage

theorem storageLive_owner_provenance {limit : Nat} {world final : World} {active after : Activation}
    {callers : List Activation} {slot : Nat} (ha : active.Valid world) (hw : world.WellFormed)
    (run : storageLive world active callers slot = some (final, after)) :
    ∀ index, LocalOwnersAbove limit world active index → LocalOwnersAbove limit final after index := by
  simp only [storageLive] at run
  split at run
  next ready =>
    simp only [bind, Option.bind_eq_some_iff] at run
    obtain ⟨current, _, suspended, _, last⟩ := run
    cases last
    intro index above
    by_cases same : index = slot
    · subst index
      exact LocalOwnersAbove.of_zero (by simp [Partial.Locals.set, Slot.dropWork])
    · obtain ⟨_, guards, frame⟩ := ha
      obtain ⟨resources, _, represented⟩ := frame.inspectSlot index
      apply LocalOwnersAbove.of_resource (active := {active with
        roots := active.roots.set slot (some ⟨world.memory.length, world.memory.length⟩), state := active.state.set slot .empty})
        ((represented.transport (world.allocate_keeps hw _ _ resources.reads).preserves).congr_at
          (by simp [Roots.set, same]) (by simp [Partial.Locals.set, same]))
      exact above resources represented
  next => cases run

theorem drop_keeps_owner_provenance {limit : Nat} {world final : World} {active after : Activation}
    {callers : List Activation} {slot other : Nat}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (different : other ≠ slot) (bounded : other < active.count)
    (above : LocalOwnersAbove limit world active other)
    (run : drop world active callers slot = some (final, after)) : LocalOwnersAbove limit final after other := by
  obtain ⟨guards, frame⟩ := ha.2
  obtain ⟨resources, _, represented⟩ := frame.inspectSlot other
  have kept := drop_preserves_other_local ha different bounded represented run
  have spec := drop_spec ha hc hw run
  have next : LocalResources final after.frame after.roots after.state other resources := by
    rw [spec.1.frame, spec.2.1]
    exact (represented.transport kept).congr_at rfl (by simp [spec.2.2.1, Partial.Locals.set, different])
  exact LocalOwnersAbove.of_resource next (above resources represented)

theorem assign_keeps_owner_provenance {limit : Nat} {world final : World} {active after : Activation}
    {callers : List Activation} {slot other : Nat} {rhs : Expr}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (bounded : other < active.count) (safe : LocalPreservation.action other (.assign slot rhs) = true)
    (above : LocalOwnersAbove limit world active other)
    (run : assign world active callers slot rhs = some (final, after)) : LocalOwnersAbove limit final after other := by
  have parts := Bool.and_eq_true_iff.mp safe
  have different : other ≠ slot := of_decide_eq_true parts.1
  have rawRun := run
  simp only [assign, bind, Option.bind_eq_some_iff] at rawRun
  obtain ⟨current, currentScan, suspended, callerScan, ⟨packet, masks⟩, expressionRun,
    remainder, remainderScan, ⟨next, state⟩, stored, last⟩ := rawRun
  have currentFrame := (Activation.scan_spec ha currentScan).frame
  obtain ⟨_, source, _, _, _⟩ := expression_spec currentFrame expressionRun
  have same := expression_local_same other parts.2 expressionRun
  obtain ⟨resources, _, represented⟩ := currentFrame.inspectSlot other
  obtain ⟨kept, frameEq, rootsEq, maskEq⟩ := assign_preserves_other_local ha hc hw source same different bounded represented run
  have next : LocalResources final after.frame after.roots after.state other resources := by
    rw [frameEq]
    exact (represented.transport kept).congr_at (congrFun rootsEq other) maskEq
  exact LocalOwnersAbove.of_resource next (above resources represented)

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
