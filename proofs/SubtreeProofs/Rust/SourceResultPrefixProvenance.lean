module

public import SubtreeProofs.Rust.SourceEvaluatorCheckpointProvenance
public import SubtreeProofs.Rust.SourceFreshWritePrefixes

/-! Move the bounded witness field out of a recursive result tuple through
actual fresh storage and cleanup. The old memo table is never required to have
bounded owners; complete source initialization justifies graph transport. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage verified_ordered_core

theorem LocalResultOwnersAbove.weaken {bound lower : Nat} {world : World} {active : Activation} {slot : Nat}
    (above : LocalResultOwnersAbove bound world active slot) (le : lower ≤ bound) :
    LocalResultOwnersAbove lower world active slot := by
  obtain ⟨cell, raw, resultCell, tableCell, shape, fresh⟩ := above
  exact ⟨cell, raw, resultCell, tableCell, shape, fun owners footprint address member => le.trans (fresh owners footprint address member)⟩

theorem LocalResultOwnersAbove.extends {bound : Nat} {world final : World} {active after : Activation} {slot : Nat} {value : Value}
    (ha : active.Valid world) (above : LocalResultOwnersAbove bound world active slot)
    (initialized : (active.state slot).materialize = some value)
    (extension : Heap.Extends world.memory final.memory) (roots : after.roots slot = active.roots slot) :
    LocalResultOwnersAbove bound final after slot := by
  obtain ⟨cell, raw, fresh⟩ := above
  obtain ⟨_, guards, frame⟩ := ha
  cases root : active.roots slot with
  | none => simp [rawAt, root] at raw
  | some binding =>
    have read : world.memory[binding.address]? = some cell := by simpa only [rawAt, root, bind, Option.bind] using raw
    obtain ⟨stored, reads, memoryRead, _, partialGraph, _⟩ := frame.get root
    have same : cell = stored := Option.some.inj (read.symm.trans memoryRead)
    have graph : Graph world.memory cell value reads := by rw [same]; exact partialGraph.materialize initialized
    exact ⟨cell, by simpa only [rawAt, roots, root, bind, Option.bind] using extension _ _ read,
      fresh.transport graph (Retains.of_extends extension reads)⟩

namespace Derived

theorem storageLive_result_owner_provenance {bound : Nat} {world final : World} {active after : Activation}
    {callers : List Activation} {source destination : Nat} {value : Value}
    (ha : active.Valid world) (above : LocalResultOwnersAbove bound world active source)
    (initialized : (active.state source).materialize = some value) (different : source ≠ destination)
    (run : storageLive world active callers destination = some (final, after)) :
    LocalResultOwnersAbove bound final after source := by
  simp only [storageLive] at run
  split at run
  next ready =>
    simp only [bind, Option.bind_eq_some_iff] at run
    obtain ⟨current, _, suspended, _, last⟩ := run
    cases last
    exact above.extends ha initialized (Heap.Extends.append _ _) (by simp [Roots.set, different])
  next => cases run

end Derived

theorem OwnerTransfer.kept {slot : Nat} {actions : List Action}
    (noCalls : Calling.noCalls (actions.foldr Control.Tree.step .done) = true)
    (safe : actions.all (LocalPreservation.action slot) = true) : OwnerTransfer slot actions slot := by
  induction actions with
  | nil => exact .nil slot
  | cons act rest ih =>
    have tailNoCalls : Calling.noCalls (rest.foldr Control.Tree.step .done) = true := by
      cases act <;> first | exact noCalls | cases noCalls
    have parts := Bool.and_eq_true_iff.mp safe
    refine .keep ?_ parts.1 (ih tailNoCalls parts.2)
    cases act <;> first | rfl | cases noCalls

namespace Calling

theorem Prefix.open_result_field_owner_provenance {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {world final : World} {active after : Activation} {bound source destination : Nat}
    {result : Option CommonEmbedding} {table : MemoTable}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (different : source ≠ destination)
    (value : active.state source = Slot.ofValue (Evaluator.encodeOutput result table))
    (above : LocalResultOwnersAbove bound world active source)
    (steps : Prefix callee callers suffix
      [.storageLive destination, .assign destination (.use (.move (.field (.local source) none 0)))] world active final after) :
    LocalOwnersAbove bound final after destination := by
  cases steps with
  | cons first rest => cases rest with
    | cons second last =>
      cases last
      simp only [instruction, Derived.instruction, bind, Option.bind_eq_some_iff] at first second
      obtain ⟨⟨openedWorld, opened⟩, opening, sameFirst⟩ := first
      cases sameFirst
      obtain ⟨⟨endingWorld, ending⟩, assigning, sameLast⟩ := second
      cases sameLast
      let code := [.storageLive destination, .assign destination (.use (.move (.field (.local source) none 0)))].foldr Control.Tree.step suffix
      have prepared := Activation.forgetRefs_valid ha code
      have mask : (active.forgetRefs code).state source = active.state source := LoanEnding.forget_closed code (List.range active.count)
        (by rw [value]; exact ofValue_typed (Evaluator.encodeOutput_typed result table))
        (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil)))
      have firstFresh := Derived.storageLive_result_owner_provenance prepared (above.memory_same rfl rfl)
        (by rw [show (active.forgetRefs code).state source = active.state source from mask, value]; exact Slot.materialize_ofValue _) different opening
      have checked := Derived.storageLive_spec prepared hc hw opening
      have finalValid := Activation.forgetRefs_valid checked.valid (.step (.assign destination (.use (.move (.field (.local source) none 0)))) suffix)
      exact Derived.assign_result_field_owner_provenance finalValid (firstFresh.memory_same rfl rfl) assigning

theorem Prefix.unpack_result_owner_provenance {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {world final : World} {active after : Activation} {bound source destination : Nat} {rest : List Action}
    {result : Option CommonEmbedding} {table : MemoTable}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (different : source ≠ destination)
    (value : active.state source = Slot.ofValue (Evaluator.encodeOutput result table))
    (above : LocalResultOwnersAbove bound world active source)
    (noCalls : Calling.noCalls (rest.foldr Control.Tree.step .done) = true)
    (safe : rest.all (LocalPreservation.action destination) = true)
    (steps : Prefix callee callers suffix
      ([.storageLive destination, .assign destination (.use (.move (.field (.local source) none 0)))] ++ rest) world active final after) :
    LocalOwnersAbove bound final after destination := by
  obtain ⟨middle, current, first, tail⟩ := steps.split
  have fresh := first.open_result_field_owner_provenance ha hc hw different value above
  obtain ⟨valid, callersValid, wellFormed⟩ := first.noncall_valid ha hc hw (by rfl)
  exact tail.owner_transfer (OwnerTransfer.kept noCalls safe) valid callersValid wellFormed fresh

theorem Prefix.retire_unpack_result_owner_provenance {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {world final : World} {active after : Activation} {bound source destination : Nat} {retired : List Nat} {rest : List Action}
    {result : Option CommonEmbedding} {table : MemoTable}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (different : source ≠ destination) (sourceKept : source ∉ retired)
    (value : active.state source = Slot.ofValue (Evaluator.encodeOutput result table))
    (above : LocalResultOwnersAbove bound world active source)
    (noCalls : Calling.noCalls (rest.foldr Control.Tree.step .done) = true)
    (safe : rest.all (LocalPreservation.action destination) = true)
    (steps : Prefix callee callers suffix
      (retired.map Action.storageDead ++
        ([.storageLive destination, .assign destination (.use (.move (.field (.local source) none 0)))] ++ rest)) world active final after) :
    LocalOwnersAbove bound final after destination := by
  obtain ⟨middle, current, first, tail⟩ := steps.split
  have onlyRetire : ∀ act ∈ retired.map Action.storageDead, ∃ slot, act = .drop slot ∨ act = .storageDead slot := by
    intro act member
    obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member
    exact ⟨slot, Or.inr rfl⟩
  have keeps : ∀ act ∈ retired.map Action.storageDead, keepsRoot source act := by
    intro act member
    obtain ⟨slot, slotMember, rfl⟩ := List.mem_map.mp member
    exact fun same => sourceKept (same.symm ▸ slotMember)
  have untouched : (retired.map Action.storageDead).all (LocalPreservation.action source) = true := by
    apply List.all_eq_true.mpr
    intro act member
    obtain ⟨slot, slotMember, rfl⟩ := List.mem_map.mp member
    simp only [LocalPreservation.action, decide_eq_true_eq]
    exact fun same => sourceKept (same.symm ▸ slotMember)
  have retiredNoCalls : Calling.noCalls ((retired.map Action.storageDead).foldr Control.Tree.step .done) = true := by
    clear sourceKept steps first onlyRetire keeps untouched
    induction retired with
    | nil => rfl
    | cons slot rest ih => exact ih
  have fresh := first.retirement_result_owner_provenance ha hc hw onlyRetire keeps above
  have nextValue := (first.closed_local_same ha hc hw (by rw [value]; exact ofValue_typed (Evaluator.encodeOutput_typed result table))
    (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) retiredNoCalls untouched).trans value
  obtain ⟨valid, callersValid, wellFormed⟩ := first.noncall_valid ha hc hw retiredNoCalls
  exact tail.unpack_result_owner_provenance valid callersValid wellFormed different nextValue fresh noCalls safe

end Calling
end SubtreeProofs.Rust.SourceEval.Addressed
