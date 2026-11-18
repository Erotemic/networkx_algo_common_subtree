module

public import SubtreeProofs.Rust.SourceEmptyRootStorage

/-! Bundle the checked typed checkpoint and an empty root for sequential actual
prefixes. Source typing supplies each later call's readiness; owner/caller models
and native evaluator contracts are unchanged. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

structure TypedRootStorage (locals : List Ty) (callers : List Activation) (world : World) (active : Activation) (slot : Nat) : Prop where
  valid : active.Valid world
  callersValid : ∀ caller ∈ callers, caller.Valid world
  wellFormed : world.WellFormed
  typed : LocalsTyped locals active.state
  storage : EmptyRootStorage world active slot

theorem TypedRootStorage.through_prefix {callee : Derived.Callees} {source : Calls}
    (respects : Derived.CallsRespect callee source Derived.TypedReady) (sourceTyped : Types.CallsTyped source)
    {world final : World} {active after : Activation} {callers : List Activation} {locals : List Ty} {slot : Nat}
    {suffix : Code} {actions : List Action} (context : TypedRootStorage locals callers world active slot)
    (steps : Calling.Prefix callee callers suffix actions world active final after)
    (constraints : ∀ act ∈ actions, Types.ActionConstraints locals act)
    (safe : ∀ act ∈ actions, LocalPreservation.action slot act = true) : TypedRootStorage locals callers final after slot := by
  obtain ⟨valid, callers, wellFormed, typed⟩ := steps.typed_spec respects sourceTyped context.valid context.callersValid context.wellFormed context.typed constraints
  exact ⟨valid, callers, wellFormed, typed, context.storage.through_prefix respects sourceTyped steps
    context.valid context.callersValid context.wellFormed context.typed constraints safe⟩

namespace Calling

theorem Prefix.opens_typed_storage {callee : Derived.Callees} {source : Calls}
    (respects : Derived.CallsRespect callee source Derived.TypedReady) (sourceTyped : Types.CallsTyped source)
    {world final : World} {active after : Activation} {callers : List Activation} {suffix : Code} {actions : List Action} {slot : Nat}
    (steps : Prefix callee callers suffix (.storageLive slot :: actions) world active final after)
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    {locals : List Ty} (typed : LocalsTyped locals active.state)
    (constraints : ∀ act ∈ .storageLive slot :: actions, Types.ActionConstraints locals act)
    (safe : ∀ act ∈ actions, LocalPreservation.action slot act = true) : TypedRootStorage locals callers final after slot := by
  obtain ⟨valid, callers, wellFormed, locals⟩ := steps.typed_spec respects sourceTyped ha hc hw typed constraints
  exact ⟨valid, callers, wellFormed, locals, steps.opens_empty_storage respects sourceTyped ha hc hw typed constraints safe⟩

end Calling
end SubtreeProofs.Rust.SourceEval.Addressed
