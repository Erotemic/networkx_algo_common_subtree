module

public import SubtreeProofs.Rust.SourceOriginalNumberView

/-! Copy a scalar into an already opened empty local through the actual checked
store. Closed source masks and original loan families remain unchanged. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem original_number_assign_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active) (callee : Derived.Callees) (suffix : Code)
    {source destination : Nat} (sourceOutside : source ∉ exceptions) (outside : destination ∉ exceptions)
    (different : source ≠ destination) {part : Slot} (initialized : active.state source = part)
    (place : Place) (selected : (splitPlace place).1 = source) {number : Nat}
    (read : part.read (splitPlace place).2 = some (.number number)) (small : number < 2^32)
    {binding : Binding} (root : active.roots destination = some binding)
    (raw : world.memory[binding.address]? = some (.node .tuple 0 [])) (empty : active.state destination = .empty) :
    ∃ final after,
      Calling.Prefix callee callers suffix [.assign destination (.use (.copy place))] world active final after ∧
      OriginalLoanMachine before callers previous external exceptions final after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      after.state source = part ∧ after.state destination = .number number ∧
      (∀ index other, index ≠ destination → active.roots index = some other → ∀ cell,
        world.memory[other.address]? = some cell → final.memory[other.address]? = some cell) := by
  let code : SourceEval.Code := .step (.assign destination (.use (.copy place))) suffix
  let prepared := active.forgetRefs code
  have machine := h.prepare code
  have sourceValue : prepared.state source = part := (h.prepare_closed_local code source sourceOutside).trans initialized
  have expression : SourceEval.expression prepared.state (.use (.copy place)) = some (.number number, prepared.state) := by
    simp only [SourceEval.expression, SourceEval.operand, Partial.Locals.read, selected, sourceValue, read,
      bind, Option.bind, small, ite_true]
  obtain ⟨cell, assigned, finalMachine⟩ := machine.assign_empty root outside raw expression
    (LoanEnding.forget_empty _ _ empty) machine.closed (by intros; rfl) trivial (.number small) .u32
  let final := world.write binding.address cell
  let after : Activation := {prepared with state := prepared.state.set destination (Slot.ofValue (.number number))}
  change OriginalLoanMachine before callers previous external exceptions final after at finalMachine
  refine ⟨final, after, .cons (Calling.instruction_noncall_run (act := .assign destination (.use (.copy place))) assigned) (.nil _ _),
    finalMachine, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simpa only [after, Partial.Locals.set, different, ite_false] using sourceValue
  · simp only [after, Partial.Locals.set, ite_true, Slot.ofValue]
  · intro index other notDestination bound value memoryRead
    exact Evaluator.Activation.write_other_root machine.native.valid root bound (Ne.symm notDestination) memoryRead cell

end SubtreeProofs.Rust.SourceEval.Addressed
