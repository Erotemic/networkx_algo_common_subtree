module

public import SubtreeProofs.Rust.SourceOriginalMoveView

/-! Open fresh storage and initialize a closed nullary constructor through
the actual executor, retaining original loan origins and older root bytes. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem original_constant_view_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active) (callee : Derived.Callees) (suffix : Code)
    {destination : Nat} (outside : destination ∉ exceptions) (kind : Kind) (tag : Nat)
    {ty : Ty} (typed : SnapshotTyped (.node kind tag []) ty) (closed : Borrow.Closed ty)
    (bound : destination < active.count) (unbound : active.roots destination = none) :
    ∃ final after,
      Calling.Prefix callee callers suffix [.storageLive destination, .assign destination (.aggregate kind tag [])]
        world active final after ∧ OriginalLoanMachine before callers previous external exceptions final after ∧
      after.roots = active.roots.set destination (some ⟨world.memory.length, world.memory.length⟩) ∧
      after.count = active.count ∧ after.frame = active.frame ∧ after.state destination = Slot.ofValue (.node kind tag []) ∧
      (∀ index binding, active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  let next : Code := .step (.assign destination (.aggregate kind tag [])) suffix
  let code : Code := .step (.storageLive destination) next
  let first := active.forgetRefs code
  have firstMachine := h.prepare code
  let openedWorld := world.allocate (.stack first.frame destination world.memory.length) (.node .tuple 0 [])
  let opened : Activation := {first with roots := first.roots.set destination (some ⟨world.memory.length, world.memory.length⟩), state := first.state.set destination .empty}
  obtain ⟨openedRun, openedMachine⟩ := firstMachine.storageLive bound unbound outside
  change OriginalLoanMachine before callers previous external exceptions openedWorld opened at openedMachine
  let prepared := opened.forgetRefs next
  have preparedMachine := openedMachine.prepare next
  have destinationRoot : prepared.roots destination = some ⟨world.memory.length, world.memory.length⟩ := by
    simp [prepared, opened, Roots.set, Activation.forgetRefs]
  have empty : prepared.state destination = .empty := by
    apply LoanEnding.forget_empty
    simp only [opened, Partial.Locals.set, ite_true]
  have source : SourceEval.expression prepared.state (.aggregate kind tag []) = some (.node kind tag [], prepared.state) := by
    simp only [SourceEval.expression, SourceEval.operands, bind, Option.bind]
  obtain ⟨cell, assigned, machine⟩ := preparedMachine.assign_empty destinationRoot outside (world.allocate_spec _ _).2.1 source empty
    preparedMachine.closed (by intros; rfl) (by simp [InlineExpr]) typed closed
  let final := openedWorld.write world.memory.length cell
  let after : Activation := {prepared with state := prepared.state.set destination (Slot.ofValue (.node kind tag []))}
  change OriginalLoanMachine before callers previous external exceptions final after at machine
  refine ⟨final, after,
    .cons (Calling.instruction_noncall_run (act := .storageLive destination) openedRun)
      (.cons (Calling.instruction_noncall_run (act := .assign destination (.aggregate kind tag [])) assigned) (.nil _ _)),
    machine, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [after, Partial.Locals.set, ite_true]
  · intro index binding atRoot raw read
    have other : index ≠ destination := by intro same; subst index; rw [unbound] at atRoot; cases atRoot
    have rootNow : prepared.roots index = some binding := by
      simpa only [prepared, opened, first, Activation.forgetRefs, Roots.set, other, ite_false] using atRoot
    exact Evaluator.Activation.write_other_root preparedMachine.native.valid destinationRoot rootNow (Ne.symm other)
      ((world.allocate_keeps h.native.wellFormed _ _ []).memory _ _ read) cell

end SubtreeProofs.Rust.SourceEval.Addressed
