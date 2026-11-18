module

public import SubtreeProofs.Rust.SourceOriginalLoanMachine
public import SubtreeProofs.Rust.SourceCacheHitProgram

/-! Open fresh stack storage and move a closed native value into it through
the actual executor. Original bounded shared loans discharge the selected
source-root permission, including when the value owns the borrowed data. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem original_move_view_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active) (callee : Derived.Callees) (suffix : Code)
    {source destination : Nat} (sourceOutside : source ∉ exceptions) (outside : destination ∉ exceptions)
    {value : Value} {ty : Ty} (initialized : active.state source = Slot.ofValue value)
    (typed : SnapshotTyped value ty) (closed : Borrow.Closed ty)
    (bound : destination < active.count) (unbound : active.roots destination = none) :
    ∃ final after,
      Calling.Prefix callee callers suffix [.storageLive destination, .assign destination (.use (.move (.local source)))]
        world active final after ∧ OriginalLoanMachine before callers previous external exceptions final after ∧
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
  obtain ⟨openedRun, openedMachine⟩ := firstMachine.storageLive bound unbound outside
  change OriginalLoanMachine before callers previous external exceptions openedWorld opened at openedMachine
  let prepared := opened.forgetRefs next
  have preparedMachine := openedMachine.prepare next
  have sourceValue : prepared.state source = Slot.ofValue value := by
    rw [openedMachine.prepare_closed_local next source sourceOutside]
    simp only [opened, Partial.Locals.set, different, ite_false]
    exact (h.prepare_closed_local code source sourceOutside).trans initialized
  have destinationRoot : prepared.roots destination = some ⟨world.memory.length, world.memory.length⟩ := by
    simp [prepared, opened, Roots.set, Activation.forgetRefs]
  have empty : (prepared.state.set source .empty) destination = .empty := by
    simp only [Partial.Locals.set, Ne.symm different, ite_false]
    apply LoanEnding.forget_empty
    simp only [opened, Partial.Locals.set, ite_true]
  obtain ⟨cell, assigned, machine⟩ := preparedMachine.assign_empty destinationRoot outside (world.allocate_spec _ _).2.1
    (Evaluator.use_local_source (state := prepared.state) (slot := source) (by rw [sourceValue]; exact Slot.materialize_ofValue _)) empty
    (preparedMachine.closed.clear source)
    (by intro index member
        have other : index ≠ source := by intro same; subst index; exact sourceOutside member
        simp only [Partial.Locals.set, other, ite_false, prepared]) trivial typed closed
  let final := openedWorld.write world.memory.length cell
  let after : Activation := {prepared with state := (prepared.state.set source .empty).set destination (Slot.ofValue value)}
  change OriginalLoanMachine before callers previous external exceptions final after at machine
  refine ⟨final, after,
    .cons (Calling.instruction_noncall_run (act := .storageLive destination) openedRun)
      (.cons (Calling.instruction_noncall_run (act := .assign destination (.use (.move (.local source)))) assigned) (.nil _ _)),
    machine, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp only [after, Partial.Locals.set, different, ite_false, ite_true]
  · simp only [after, Partial.Locals.set, ite_true]
  · intro index binding atRoot raw read
    have other : index ≠ destination := by intro same; subst index; rw [unbound] at atRoot; cases atRoot
    have rootNow : prepared.roots index = some binding := by
      simpa only [prepared, opened, first, Activation.forgetRefs, Roots.set, other, ite_false] using atRoot
    exact Evaluator.Activation.write_other_root preparedMachine.native.valid destinationRoot rootNow (Ne.symm other)
      ((world.allocate_keeps h.native.wellFormed _ _ []).memory _ _ read) cell

end SubtreeProofs.Rust.SourceEval.Addressed
