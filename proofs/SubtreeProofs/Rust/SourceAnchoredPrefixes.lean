module

public import SubtreeProofs.Rust.SourceAnchoredAssignments
public import SubtreeProofs.Rust.SourcePrefixCallPreservation
public import SubtreeProofs.Rust.SourceCacheHitScope

/-! Construct actual stack-opening, original-query reborrow and closed-value
move prefixes while a separate owned word supports fresh shared references. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage verified_ordered_core

theorem anchored_open_local_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external original fresh : List Nat} {anchorSlot : Nat} {word : BalancedWord} {anchor : Resources}
    (h : AnchoredLoanMachine before callers previous external original fresh anchorSlot word anchor world active)
    (callee : Derived.Callees) (suffix : Code) {slot : Nat}
    (outside : slot ∉ fresh ++ original) (different : anchorSlot ≠ slot)
    (bound : slot < active.count) (unbound : active.roots slot = none) :
    ∃ final after,
      Calling.Prefix callee callers suffix [.storageLive slot] world active final after ∧
      AnchoredLoanMachine before callers previous external original fresh anchorSlot word anchor final after ∧
      after.roots = active.roots.set slot (some ⟨world.memory.length, world.memory.length⟩) ∧
      after.count = active.count ∧ after.frame = active.frame ∧ after.state slot = .empty ∧
      final.memory[world.memory.length]? = some (.node .tuple 0 []) ∧
      (∀ index binding, active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  let code : Code := .step (.storageLive slot) suffix
  have machine := h.prepare code
  obtain ⟨run, finalMachine⟩ := machine.storageLive bound unbound outside different
  refine ⟨_, _, .cons (Calling.instruction_noncall_run (act := .storageLive slot) run) (.nil _ _),
    finalMachine, rfl, rfl, rfl, ?_, (world.allocate_spec _ _).2.1, ?_⟩
  · simp only [Partial.Locals.set, ite_true]
  · intro index binding root raw memoryRead
    exact (world.allocate_keeps h.native.wellFormed _ _ []).memory _ _ memoryRead

theorem anchored_original_borrow_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external original fresh : List Nat} {anchorSlot : Nat} {word : BalancedWord} {anchor : Resources}
    (h : AnchoredLoanMachine before callers previous external original fresh anchorSlot word anchor world active)
    (callee : Derived.Callees) (suffix : Code) {slot destination : Nat}
    (member : slot ∈ original) (outside : destination ∉ fresh ++ original) (anchorDifferent : anchorSlot ≠ destination)
    {path : List Projection} {place : Place} (split : splitPlace place = (slot, path))
    (route : SharedRoute (active.state slot) path) {value : Value} (source : active.state.read place = some value)
    (data : NativeData value) (bound : destination < active.count) (unbound : active.roots destination = none) :
    ∃ final after,
      Calling.Prefix callee callers suffix [.storageLive destination, .assign destination (.address place)] world active final after ∧
      AnchoredLoanMachine before callers previous external (destination :: original) fresh anchorSlot word anchor final after ∧
      after.roots = active.roots.set destination (some ⟨world.memory.length, world.memory.length⟩) ∧
      after.count = active.count ∧ after.frame = active.frame ∧ after.state destination = .shared value ∧
      (∀ index binding, active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  have different : slot ≠ destination := by intro same; subst slot; exact outside (List.mem_append_right fresh member)
  let next : Code := .step (.assign destination (.address place)) suffix
  let code : Code := .step (.storageLive destination) next
  have observed : LoanEnding.endsBeforeObservation slot code = false := by
    simp [code, next, LoanEnding.endsBeforeObservation, LoanEnding.avoidsAction, LoanEnding.writes,
      LoanEnding.avoidsExpr, LoanEnding.avoidsPlace, split, Ne.symm different]
  have nextObserved : LoanEnding.endsBeforeObservation slot next = false := by
    simp [next, LoanEnding.endsBeforeObservation, LoanEnding.avoidsAction, LoanEnding.avoidsExpr, LoanEnding.avoidsPlace, split]
  let first := active.forgetRefs code
  have firstMachine := h.prepare code
  let openedWorld := world.allocate (.stack first.frame destination world.memory.length) (.node .tuple 0 [])
  let opened : Activation := {first with roots := first.roots.set destination (some ⟨world.memory.length, world.memory.length⟩), state := first.state.set destination .empty}
  obtain ⟨openedRun, openedMachine⟩ := firstMachine.storageLive bound unbound outside anchorDifferent
  change AnchoredLoanMachine before callers previous external original fresh anchorSlot word anchor openedWorld opened at openedMachine
  let prepared := opened.forgetRefs next
  have preparedMachine := openedMachine.prepare next
  have sourceMask : prepared.state slot = active.state slot := by
    rw [Activation.forgetRefs_observed opened next slot nextObserved]
    simp only [opened, Partial.Locals.set, different, ite_false]
    exact Activation.forgetRefs_observed active code slot observed
  have routeNow : SharedRoute (prepared.state slot) path := sourceMask ▸ route
  have sourceNow : prepared.state.read place = some value := by simpa only [Partial.Locals.read, split, sourceMask] using source
  have destinationRoot : prepared.roots destination = some ⟨world.memory.length, world.memory.length⟩ := by
    simp [prepared, opened, Roots.set, Activation.forgetRefs]
  have empty : prepared.state destination = .empty := by
    apply LoanEnding.forget_empty
    simp only [opened, Partial.Locals.set, ite_true]
  obtain ⟨pointer, assigned, finalMachine, rawDestination⟩ := preparedMachine.assign_original_view member outside anchorDifferent split routeNow sourceNow data
    destinationRoot (world.allocate_spec _ _).2.1 empty
  let final := openedWorld.write world.memory.length (.shared pointer)
  let after : Activation := {prepared with state := prepared.state.set destination (.shared value)}
  refine ⟨final, after,
    .cons (Calling.instruction_noncall_run (act := .storageLive destination) openedRun)
      (.cons (Calling.instruction_noncall_run (act := .assign destination (.address place)) assigned) (.nil _ _)),
    finalMachine, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [after, Partial.Locals.set, ite_true]
  · intro index binding root raw memoryRead
    have other : index ≠ destination := by intro same; subst index; rw [unbound] at root; cases root
    have rootNow : prepared.roots index = some binding := by
      simpa only [prepared, opened, first, Activation.forgetRefs, Roots.set, other, ite_false] using root
    exact Evaluator.Activation.write_other_root preparedMachine.native.valid destinationRoot rootNow (Ne.symm other)
      ((world.allocate_keeps h.native.wellFormed _ _ []).memory _ _ memoryRead) (.shared pointer)

theorem anchored_move_view_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external original fresh : List Nat} {anchorSlot : Nat} {word : BalancedWord} {anchor : Resources}
    (h : AnchoredLoanMachine before callers previous external original fresh anchorSlot word anchor world active)
    (callee : Derived.Callees) (suffix : Code) {source destination : Nat}
    (sourceOutside : source ∉ fresh ++ original) (outside : destination ∉ fresh ++ original)
    (anchorSource : anchorSlot ≠ source) (anchorDestination : anchorSlot ≠ destination)
    {value : Value} {ty : Ty} (initialized : active.state source = Slot.ofValue value)
    (typed : SnapshotTyped value ty) (closed : Borrow.Closed ty)
    (bound : destination < active.count) (unbound : active.roots destination = none) :
    ∃ final after,
      Calling.Prefix callee callers suffix [.storageLive destination, .assign destination (.use (.move (.local source)))] world active final after ∧
      AnchoredLoanMachine before callers previous external original fresh anchorSlot word anchor final after ∧
      after.roots = active.roots.set destination (some ⟨world.memory.length, world.memory.length⟩) ∧
      after.count = active.count ∧ after.frame = active.frame ∧ after.state source = .empty ∧ after.state destination = Slot.ofValue value ∧
      (∀ index binding, active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  have different : source ≠ destination := by
    intro same; subst source
    obtain ⟨_, frame⟩ := h.native.valid.2
    have empty : active.state destination = .empty := by simpa only [unbound] using frame.slots destination
    have materialized := Slot.materialize_ofValue value
    rw [← initialized, empty] at materialized
    simp only [Slot.materialize, reduceCtorEq] at materialized
  let next : Code := .step (.assign destination (.use (.move (.local source)))) suffix
  let code : Code := .step (.storageLive destination) next
  let first := active.forgetRefs code
  have firstMachine := h.prepare code
  let openedWorld := world.allocate (.stack first.frame destination world.memory.length) (.node .tuple 0 [])
  let opened : Activation := {first with roots := first.roots.set destination (some ⟨world.memory.length, world.memory.length⟩), state := first.state.set destination .empty}
  obtain ⟨openedRun, openedMachine⟩ := firstMachine.storageLive bound unbound outside anchorDestination
  change AnchoredLoanMachine before callers previous external original fresh anchorSlot word anchor openedWorld opened at openedMachine
  let prepared := opened.forgetRefs next
  have preparedMachine := openedMachine.prepare next
  have firstSame : first.state source = active.state source := LoanEnding.forget_closed _ _ (by rw [initialized]; exact ofValue_typed typed) closed
  have openedSame : opened.state source = active.state source := by
    simpa only [opened, Partial.Locals.set, different, ite_false] using firstSame
  have sourceValue : prepared.state source = Slot.ofValue value := by
    have preparedSame : prepared.state source = opened.state source :=
      LoanEnding.forget_closed _ _ (by rw [openedSame, initialized]; exact ofValue_typed typed) closed
    exact preparedSame.trans (openedSame.trans initialized)
  have destinationRoot : prepared.roots destination = some ⟨world.memory.length, world.memory.length⟩ := by
    simp [prepared, opened, Roots.set, Activation.forgetRefs]
  have empty : (prepared.state.set source .empty) destination = .empty := by
    simp only [Partial.Locals.set, Ne.symm different, ite_false]
    apply LoanEnding.forget_empty
    simp only [opened, Partial.Locals.set, ite_true]
  obtain ⟨sourceRoot, atSource⟩ := Activation.root_of_materialize preparedMachine.native.valid
    (by rw [sourceValue]; exact Slot.materialize_ofValue _)
  obtain ⟨cell, assigned, machine⟩ := preparedMachine.assign_empty destinationRoot outside anchorDestination (world.allocate_spec _ _).2.1
    (Evaluator.use_local_source (state := prepared.state) (slot := source) (by rw [sourceValue]; exact Slot.materialize_ofValue _)) empty
    (preparedMachine.closed.clear source)
    (by intro index member
        have other : index ≠ source := by intro same; subst index; exact sourceOutside member
        simp only [prepared, Partial.Locals.set, other, ite_false])
    (by simp only [prepared, Partial.Locals.set, anchorSource, ite_false]) (preparedMachine.native.safe.clear source)
    (fun _ _ scanned callerView => preparedMachine.move_local atSource anchorSource scanned callerView) typed closed
  let final := openedWorld.write world.memory.length cell
  let after : Activation := {prepared with state := (prepared.state.set source .empty).set destination (Slot.ofValue value)}
  refine ⟨final, after,
    .cons (Calling.instruction_noncall_run (act := .storageLive destination) openedRun)
      (.cons (Calling.instruction_noncall_run (act := .assign destination (.use (.move (.local source)))) assigned) (.nil _ _)),
    machine, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp only [after, Partial.Locals.set, different, ite_false, ite_true]
  · simp only [after, Partial.Locals.set, ite_true]
  · intro index binding root raw memoryRead
    have other : index ≠ destination := by intro same; subst index; rw [unbound] at root; cases root
    have rootNow : prepared.roots index = some binding := by
      simpa only [prepared, opened, first, Activation.forgetRefs, Roots.set, other, ite_false] using root
    exact Evaluator.Activation.write_other_root preparedMachine.native.valid destinationRoot rootNow (Ne.symm other)
      ((world.allocate_keeps h.native.wellFormed _ _ []).memory _ _ memoryRead) cell

end SubtreeProofs.Rust.SourceEval.Addressed
