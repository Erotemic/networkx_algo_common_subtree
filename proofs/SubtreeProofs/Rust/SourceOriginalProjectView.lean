module

public import SubtreeProofs.Rust.SourceOriginalMoveView

/-! Fresh storage receives an actual inline partial move from a closed local.
The maintained remaining mask and its closed type stay explicit; canonical
original-loan inventories discharge source and destination permissions. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem original_project_view_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active) (callee : Derived.Callees) (suffix : Code)
    {source destination : Nat} (sourceOutside : source ∉ exceptions) (outside : destination ∉ exceptions) (different : source ≠ destination)
    {path : List Projection} {place : Place} (split : splitPlace place = (source, path)) (inlinePlace : InlinePlace place)
    {value : Value} {remaining : Slot} (take : (active.state source).take path = some (value, remaining))
    {sourceTy ty : Ty} (remainingTyped : SlotTyped remaining sourceTy) (remainingClosed : Borrow.Closed sourceTy)
    (typed : SnapshotTyped value ty) (closed : Borrow.Closed ty)
    (bound : destination < active.count) (unbound : active.roots destination = none) :
    ∃ final after,
      Calling.Prefix callee callers suffix [.storageLive destination, .assign destination (.use (.move place))]
        world active final after ∧ OriginalLoanMachine before callers previous external exceptions final after ∧
      after.roots = active.roots.set destination (some ⟨world.memory.length, world.memory.length⟩) ∧
      after.count = active.count ∧ after.frame = active.frame ∧ after.state source = remaining ∧ after.state destination = Slot.ofValue value ∧
      (∀ index binding, active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  let next : Code := .step (.assign destination (.use (.move place))) suffix
  let code : Code := .step (.storageLive destination) next
  let first := active.forgetRefs code
  have firstMachine := h.prepare code
  let openedWorld := world.allocate (.stack first.frame destination world.memory.length) (.node .tuple 0 [])
  let opened : Activation := {first with roots := first.roots.set destination (some ⟨world.memory.length, world.memory.length⟩), state := first.state.set destination .empty}
  obtain ⟨openedRun, openedMachine⟩ := firstMachine.storageLive bound unbound outside
  change OriginalLoanMachine before callers previous external exceptions openedWorld opened at openedMachine
  let prepared := opened.forgetRefs next
  have preparedMachine := openedMachine.prepare next
  have sourceMask : prepared.state source = active.state source := by
    rw [openedMachine.prepare_closed_local next source sourceOutside]
    simp only [opened, Partial.Locals.set, different, ite_false]
    exact h.prepare_closed_local code source sourceOutside
  have sourceRun : SourceEval.expression prepared.state (.use (.move place)) = some (value, prepared.state.set source remaining) := by
    simp only [SourceEval.expression, SourceEval.operand, Partial.Locals.move, split, sourceMask, take, bind, Option.bind]
  have destinationRoot : prepared.roots destination = some ⟨world.memory.length, world.memory.length⟩ := by
    simp [prepared, opened, Roots.set, Activation.forgetRefs]
  have empty : (prepared.state.set source remaining) destination = .empty := by
    simp only [Partial.Locals.set, Ne.symm different, ite_false]
    apply LoanEnding.forget_empty
    simp only [opened, Partial.Locals.set, ite_true]
  obtain ⟨cell, assigned, machine⟩ := preparedMachine.assign_empty destinationRoot outside (world.allocate_spec _ _).2.1 sourceRun empty
    (preparedMachine.closed.set source remainingTyped remainingClosed)
    (by intro index member
        have other : index ≠ source := by intro same; subst index; exact sourceOutside member
        simp only [Partial.Locals.set, other, ite_false, prepared]) inlinePlace typed closed
  let final := openedWorld.write world.memory.length cell
  let after : Activation := {prepared with state := (prepared.state.set source remaining).set destination (Slot.ofValue value)}
  change OriginalLoanMachine before callers previous external exceptions final after at machine
  refine ⟨final, after,
    .cons (Calling.instruction_noncall_run (act := .storageLive destination) openedRun)
      (.cons (Calling.instruction_noncall_run (act := .assign destination (.use (.move place))) assigned) (.nil _ _)),
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
