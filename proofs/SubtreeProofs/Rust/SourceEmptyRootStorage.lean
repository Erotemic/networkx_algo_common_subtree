module

public import SubtreeProofs.Rust.SourceTypedPrefixes
public import SubtreeProofs.Rust.SourcePrefixCallPreservation

/-! Empty logical storage and its actual empty root bytes form a separate
invariant. Checked source typing derives call readiness for its preservation;
actual storage-live establishes the invariant without a desired post-frame. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

structure EmptyRootStorage (world : World) (active : Activation) (slot : Nat) : Prop where
  empty : active.state slot = .empty
  root : ∃ binding, active.roots slot = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])

theorem EmptyRootStorage.through_prefix {callee : Derived.Callees} {source : Calls}
    (respects : Derived.CallsRespect callee source Derived.TypedReady) (sourceTyped : Types.CallsTyped source)
    {world final : World} {active after : Activation} {callers : List Activation} {suffix : Code} {actions : List Action}
    {slot : Nat} (storage : EmptyRootStorage world active slot)
    (steps : Calling.Prefix callee callers suffix actions world active final after)
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    {locals : List Ty} (typed : LocalsTyped locals active.state)
    (constraints : ∀ act ∈ actions, Types.ActionConstraints locals act)
    (safe : ∀ act ∈ actions, LocalPreservation.action slot act = true) : EmptyRootStorage final after slot := by
  obtain ⟨binding, root, raw⟩ := storage.root
  obtain ⟨rootAfter, rawAfter⟩ := steps.typed_other_root respects sourceTyped ha hc hw typed constraints root raw
    (fun act member => LocalPreservation.action_no_write slot (safe act member))
  exact ⟨(steps.closed_local_same_calls (by rw [storage.empty]; exact .empty .u32) .u32
    (List.all_eq_true.mpr safe)).trans storage.empty, binding, rootAfter, rawAfter⟩

namespace Calling

theorem Prefix.opens_empty_storage {callee : Derived.Callees} {source : Calls}
    (respects : Derived.CallsRespect callee source Derived.TypedReady) (sourceTyped : Types.CallsTyped source)
    {world final : World} {active after : Activation} {callers : List Activation} {suffix : Code} {actions : List Action} {slot : Nat}
    (steps : Prefix callee callers suffix (.storageLive slot :: actions) world active final after)
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    {locals : List Ty} (typed : LocalsTyped locals active.state)
    (constraints : ∀ act ∈ .storageLive slot :: actions, Types.ActionConstraints locals act)
    (safe : ∀ act ∈ actions, LocalPreservation.action slot act = true) : EmptyRootStorage final after slot := by
  cases steps with
  | cons first tail =>
    let code := (.storageLive slot :: actions).foldr Control.Tree.step suffix
    let prepared := active.forgetRefs code
    have valid := Activation.forgetRefs_valid ha code
    have localTypes := Activation.forgetRefs_typed typed code
    have checked := noncall_spec (source := source) valid hc hw (.storageLive slot) first
    have nextTyped := Types.action_typed sourceTyped localTypes (.storageLive slot) (constraints _ (by simp)) checked.source
    simp only [instruction, Derived.instruction, bind, Option.bind_eq_some_iff] at first
    obtain ⟨⟨w, a⟩, acted, same⟩ := first
    cases same
    simp only [Derived.action, Derived.storageLive] at acted
    split at acted
    next accepted =>
      simp only [bind, Option.bind_eq_some_iff] at acted
      obtain ⟨current, scanned, suspended, callerScan, last⟩ := acted
      cases last
      let openedWorld := world.allocate (.stack prepared.frame slot world.memory.length) (.node .tuple 0 [])
      let opened : Activation := {prepared with roots := prepared.roots.set slot (some ⟨world.memory.length, world.memory.length⟩), state := prepared.state.set slot .empty}
      have openedStorage : EmptyRootStorage openedWorld opened slot := by
        refine ⟨?_, ⟨world.memory.length, world.memory.length⟩, ?_, (world.allocate_spec _ _).2.1⟩
        · simp only [opened, Partial.Locals.set, ite_true]
        · simp only [opened, Roots.set, ite_true]
      exact openedStorage.through_prefix respects sourceTyped tail checked.valid checked.callers checked.wellFormed nextTyped
        (fun act member => constraints act (List.mem_cons_of_mem _ member)) safe
    next => cases acted

end Calling
end SubtreeProofs.Rust.SourceEval.Addressed
