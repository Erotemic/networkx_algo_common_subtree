module

public import SubtreeProofs.Rust.SourceRetainedOwnerProvenance

/-! A partial move leaves only owners from the source. Guarded storage retains
those remaining owners at every other local, even when its source mask changed.
This permits an owned sibling to be destroyed after extracting a tuple field. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage

theorem assign_operand_remaining_owner_provenance {bound : Nat} {world final : World}
    {active after : Activation} {callers : List Activation} {slot other : Nat} {op : Operand}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (different : other ≠ slot) (bounded : other < active.count)
    (above : LocalOwnersAbove bound world active other)
    (run : assign world active callers slot (.use op) = some (final, after)) :
    LocalOwnersAbove bound final after other := by
  simp only [assign, bind, Option.bind_eq_some_iff] at run
  obtain ⟨current, currentScan, suspended, callerScan, ⟨packet, masks⟩, expressionRun,
    remainder, remainderScan, ⟨next, state⟩, stored, last⟩ := run
  cases last
  have frame := (Activation.scan_spec ha currentScan).frame
  have callerView := scanCallers_spec hc callerScan
  have remainingAbove := (operand_owner_provenance (bound := bound) ha expressionRun).1 other above
  obtain ⟨_, _, _, _, masksFrame⟩ := Addressed.expression_spec frame expressionRun
  let middle : Activation := {active with state := masks}
  have middleValid : middle.Valid world := ⟨ha.1, _, masksFrame⟩
  obtain ⟨actual, scanned, inventory, context⟩ := middle.context_complete middleValid slot
  have same : actual = remainder := Option.some.inj (scanned.symm.trans remainderScan)
  subst actual
  obtain ⟨item, represented, included, _, _⟩ := inventory.get (slot := other)
    (by change other ∈ remainingSlots active.count slot; simp [remainingSlots, bounded, different])
  have enlarged := context.weaken (fun _ member => List.mem_append_left _ member) (by
    intro address member
    rcases List.mem_append.mp member with own | old
    · exact context.alive address own
    · exact callerView.alive address old)
  have packetRead := (Addressed.expression_readable frame expressionRun).2.1
  have spec := store_spec hw enlarged packetRead stored
  have kept := spec.2.2.1.weaken (fun _ member => List.mem_append_left _ (included member))
  have nextRep : LocalResources next active.frame active.roots state other item := by
    apply (represented.transport kept).congr_at rfl
    rw [spec.1]
    simp only [Partial.Locals.set, different, ite_false]
  exact LocalOwnersAbove.of_resource nextRep (remainingAbove item represented)

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
