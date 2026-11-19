module

public import SubtreeProofs.Rust.SourceOriginalConstantView

/-! Copy an in-range scalar field into fresh actual local storage. The source
is independently typed and closed; original borrowed query families persist. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem original_number_copy_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active) (callee : Derived.Callees) (suffix : Code)
    {source destination : Nat} (sourceOutside : source ∉ exceptions) (outside : destination ∉ exceptions)
    (different : source ≠ destination) {part : Slot}
    (initialized : active.state source = part)
    (place : Place) (selected : (splitPlace place).1 = source) {number : Nat}
    (read : part.read (splitPlace place).2 = some (.number number)) (small : number < 2^32)
    (bound : destination < active.count) (unbound : active.roots destination = none) :
    ∃ final after,
      Calling.Prefix callee callers suffix [.storageLive destination, .assign destination (.use (.copy place))]
        world active final after ∧ OriginalLoanMachine before callers previous external exceptions final after ∧
      after.roots = active.roots.set destination (some ⟨world.memory.length, world.memory.length⟩) ∧
      after.count = active.count ∧ after.frame = active.frame ∧ after.state source = part ∧
      after.state destination = .number number ∧
      (∀ index binding, active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  let next : Code := .step (.assign destination (.use (.copy place))) suffix
  let code : Code := .step (.storageLive destination) next
  let first := active.forgetRefs code
  have firstMachine := h.prepare code
  let openedWorld := world.allocate (.stack first.frame destination world.memory.length) (.node .tuple 0 [])
  let opened : Activation := {first with roots := first.roots.set destination (some ⟨world.memory.length, world.memory.length⟩), state := first.state.set destination .empty}
  obtain ⟨openedRun, openedMachine⟩ := firstMachine.storageLive bound unbound outside
  change OriginalLoanMachine before callers previous external exceptions openedWorld opened at openedMachine
  let prepared := opened.forgetRefs next
  have preparedMachine := openedMachine.prepare next
  have sourceValue : prepared.state source = part := by
    rw [openedMachine.prepare_closed_local next source sourceOutside]
    simp only [opened, Partial.Locals.set, different, ite_false]
    exact (h.prepare_closed_local code source sourceOutside).trans initialized
  have destinationRoot : prepared.roots destination = some ⟨world.memory.length, world.memory.length⟩ := by
    simp [prepared, opened, Roots.set, Activation.forgetRefs]
  have empty : prepared.state destination = .empty := by
    apply LoanEnding.forget_empty
    simp only [opened, Partial.Locals.set, ite_true]
  have expression : SourceEval.expression prepared.state (.use (.copy place)) = some (.number number, prepared.state) := by
    simp only [SourceEval.expression, SourceEval.operand, Partial.Locals.read, selected, sourceValue, read,
      bind, Option.bind, small, ite_true]
  obtain ⟨cell, assigned, machine⟩ := preparedMachine.assign_empty destinationRoot outside (world.allocate_spec _ _).2.1
    expression empty preparedMachine.closed (by intros; rfl) trivial (.number small) .u32
  let final := openedWorld.write world.memory.length cell
  let after : Activation := {prepared with state := prepared.state.set destination (Slot.ofValue (.number number))}
  change OriginalLoanMachine before callers previous external exceptions final after at machine
  refine ⟨final, after,
    .cons (Calling.instruction_noncall_run (act := .storageLive destination) openedRun)
      (.cons (Calling.instruction_noncall_run (act := .assign destination (.use (.copy place))) assigned) (.nil _ _)),
    machine, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simpa only [after, Partial.Locals.set, different, ite_false] using sourceValue
  · simp only [after, Partial.Locals.set, ite_true, Slot.ofValue]
  · intro index binding atRoot raw memoryRead
    have other : index ≠ destination := by intro same; subst index; rw [unbound] at atRoot; cases atRoot
    have rootNow : prepared.roots index = some binding := by
      simpa only [prepared, opened, first, Activation.forgetRefs, Roots.set, other, ite_false] using atRoot
    exact Evaluator.Activation.write_other_root preparedMachine.native.valid destinationRoot rootNow (Ne.symm other)
      ((world.allocate_keeps h.native.wellFormed _ _ []).memory _ _ memoryRead) cell

end SubtreeProofs.Rust.SourceEval.Addressed
