module

public import SubtreeProofs.Rust.SourcePrefixLocals

/-! Untouched closed locals retain their types and masks through actual
non-call prefixes, including opening additional reference-view exceptions. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource Heap Partial Partial.Addressed Storage

theorem Prefix.closed_outside {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {actions : List Action} {world final : World} {active after : Activation} {exceptions : List Nat}
    (h : Prefix callee callers suffix actions world active final after)
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (closed : ClosedOutside exceptions active.state)
    (noCalls : Calling.noCalls (actions.foldr Control.Tree.step .done) = true)
    (unchanged : ∀ index, index ∉ exceptions → actions.all (LocalPreservation.action index) = true) :
    ClosedOutside exceptions after.state := by
  intro index outside
  obtain ⟨ty, typed, shape⟩ := closed index outside
  have same := h.closed_local_same ha hc hw typed shape noCalls (unchanged index outside)
  exact ⟨ty, by rw [same]; exact typed, shape⟩

theorem Prefix.open_view_closed {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {world final : World} {active after : Activation} {exceptions : List Nat} {destination : Nat} {place : Place}
    (h : Prefix callee callers suffix [.storageLive destination, .assign destination (.address place)] world active final after)
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (closed : ClosedOutside exceptions active.state) (member : destination ∈ exceptions) : ClosedOutside exceptions after.state := by
  apply h.closed_outside ha hc hw closed rfl
  intro index outside
  have different : index ≠ destination := by intro same; subst index; exact outside member
  simp [LocalPreservation.action, LocalPreservation.expression, different]

end SubtreeProofs.Rust.SourceEval.Addressed.Calling
