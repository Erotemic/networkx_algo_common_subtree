module

public import SubtreeProofs.Rust.SourceStoreTotality

/-! A call protects exactly the post-argument context, suspended reads and the
empty destination root. Those resources reconstruct the full suspended active
frame after the callee. Canonical inventories transport destination loan
permissions without a supplied post-callee frame or rescan oracle. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open Heap

theorem Inventory.unique {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals}
    {slots : List Nat} {first second : Resources}
    (h : Inventory world frame roots state slots first) (other : Inventory world frame roots state slots second) :
    first = second := Option.some.inj (h.inspect.symm.trans other.inspect)

theorem Frame.restore_empty {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals}
    {guards retained : List Nat} (h : Frame world frame roots state guards)
    {slot : Nat} {binding : Binding} (hb : roots slot = some binding) (empty : state slot = .empty)
    (context : Frame world frame (roots.set slot none) (state.set slot .empty) retained) :
    Frame world frame roots state (retained ++ [binding.address]) := by
  obtain ⟨cell, _, raw, classified, _, subset⟩ := h.get hb
  have rootLive := h.alive binding.address (subset (List.mem_append_right _ (by simp)))
  have alive : AliveOn world.live (retained ++ [binding.address]) := by
    intro address member
    rcases List.mem_append.mp member with old | root
    · exact context.alive address old
    · simpa only [List.mem_singleton.mp root] using rootLive
  have enlarged := context.weaken (fun _ member => List.mem_append_left _ member) alive
  refine ⟨alive, ?_⟩
  intro index
  by_cases same : index = slot
  · subst index
    simp only [hb, empty]
    exact ⟨cell, [], raw, classified, .empty cell, fun _ member => List.mem_append_right _ member⟩
  · simpa only [Roots.set, Partial.Locals.set, same, ite_false] using enlarged.slots index

theorem Activation.preserve_call_context {before after : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid before) {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding)
    (empty : active.state slot = .empty) {remainder suspended : Resources}
    (remaining : Inventory before active.frame active.roots active.state (remainingSlots active.count slot) remainder)
    (callerView : Callers before callers suspended)
    (kept : Preserves before after ((remainder.reads ++ suspended.reads) ++ [binding.address])) :
    active.Valid after := by
  obtain ⟨_, frame⟩ := ha.2
  have context := remaining.context frame ha.1
  have enlarged := context.weaken (fun _ member => List.mem_append_left _ member) (by
    intro address member
    rcases List.mem_append.mp member with own | old
    · exact remaining.alive address own
    · exact callerView.alive address old)
  exact ⟨ha.1, _, (frame.restore_empty hb empty enlarged).preserve kept⟩

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage

theorem RootLoansAllowed.transport {before after : World} {active : Activation} {callers : List Activation}
    {slot : Nat} {binding : Binding} {remainder suspended : Resources}
    (h : RootLoansAllowed before active callers slot binding)
    (remaining : Inventory before active.frame active.roots active.state (remainingSlots active.count slot) remainder)
    (callerView : Callers before callers suspended)
    (kept : Preserves before after (remainder.reads ++ suspended.reads)) :
    RootLoansAllowed after active callers slot binding := by
  intro current old currentView oldView
  have same := currentView.unique (remaining.transport (kept.weaken (fun _ member => List.mem_append_left _ member)))
  have callersSame := oldView.unique (callerView.transport (kept.weaken (fun _ member => List.mem_append_right _ member)))
  rw [same, callersSame]
  exact h remainder suspended remaining callerView

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
