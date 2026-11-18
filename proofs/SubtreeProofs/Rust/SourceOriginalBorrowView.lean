module

public import SubtreeProofs.Rust.SourceOriginalReborrow
public import SubtreeProofs.Rust.SourcePrefixUnshared

/-! Open and assign one actual shared view of a source place. The original-loan
family is extended by the destination; every older bound root retains its raw
cell and the actual continuation determines reference preparation. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem original_borrow_view_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active) (callee : Derived.Callees) (suffix : Code)
    {slot destination : Nat} (member : slot ∈ exceptions) (outside : destination ∉ exceptions)
    {path : List Projection} {place : Place} (split : splitPlace place = (slot, path))
    (route : SharedRoute (active.state slot) path) {value : Value} (source : active.state.read place = some value)
    (data : NativeData value) (bound : destination < active.count) (unbound : active.roots destination = none) :
    ∃ final after,
      Calling.Prefix callee callers suffix [.storageLive destination, .assign destination (.address place)] world active final after ∧
      OriginalLoanMachine before callers previous external (destination :: exceptions) final after ∧
      after.roots = active.roots.set destination (some ⟨world.memory.length, world.memory.length⟩) ∧
      after.count = active.count ∧ after.frame = active.frame ∧ after.state destination = .shared value ∧
      (∀ index binding, active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  have different : slot ≠ destination := by intro same; subst slot; exact outside member
  let next : Code := .step (.assign destination (.address place)) suffix
  let code : Code := .step (.storageLive destination) next
  have observed : LoanEnding.endsBeforeObservation slot code = false := by
    simp [code, next, LoanEnding.endsBeforeObservation, LoanEnding.avoidsAction, LoanEnding.writes,
      LoanEnding.avoidsExpr, LoanEnding.avoidsPlace, split, Ne.symm different]
  have nextObserved : LoanEnding.endsBeforeObservation slot next = false := by
    simp [next, LoanEnding.endsBeforeObservation, LoanEnding.avoidsAction, LoanEnding.avoidsExpr,
      LoanEnding.avoidsPlace, split]
  let first := active.forgetRefs code
  have firstMachine := h.prepare code
  let openedWorld := world.allocate (.stack first.frame destination world.memory.length) (.node .tuple 0 [])
  let opened : Activation := {first with roots := first.roots.set destination (some ⟨world.memory.length, world.memory.length⟩), state := first.state.set destination .empty}
  obtain ⟨openedRun, openedMachine⟩ := firstMachine.storageLive bound unbound outside
  change OriginalLoanMachine before callers previous external exceptions openedWorld opened at openedMachine
  let prepared := opened.forgetRefs next
  have preparedMachine := openedMachine.prepare next
  have sourceMask : prepared.state slot = active.state slot := by
    rw [Activation.forgetRefs_observed opened next slot nextObserved]
    simp only [opened, Partial.Locals.set, different, ite_false]
    exact Activation.forgetRefs_observed active code slot observed
  have routeNow : SharedRoute (prepared.state slot) path := sourceMask ▸ route
  have sourceNow : prepared.state.read place = some value := by
    simpa only [Partial.Locals.read, split, sourceMask] using source
  have destinationRoot : prepared.roots destination = some ⟨world.memory.length, world.memory.length⟩ := by
    simp [prepared, opened, Roots.set, Activation.forgetRefs]
  have empty : prepared.state destination = .empty := by
    apply LoanEnding.forget_empty
    simp only [opened, Partial.Locals.set, ite_true]
  obtain ⟨pointer, assigned, finalMachine, rawDestination⟩ := preparedMachine.assign_borrow member outside split routeNow sourceNow data
    destinationRoot (world.allocate_spec _ _).2.1 empty
  let final := openedWorld.write world.memory.length (.shared pointer)
  let after : Activation := {prepared with state := prepared.state.set destination (.shared value)}
  change OriginalLoanMachine before callers previous external (destination :: exceptions) final after at finalMachine
  refine ⟨final, after,
    .cons (Calling.instruction_noncall_run (act := .storageLive destination) openedRun)
      (.cons (Calling.instruction_noncall_run (act := .assign destination (.address place)) assigned) (.nil _ _)),
    finalMachine, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [after, Partial.Locals.set, ite_true]
  · intro index binding atRoot raw read
    have other : index ≠ destination := by intro same; subst index; rw [unbound] at atRoot; cases atRoot
    have rootNow : prepared.roots index = some binding := by
      simpa only [prepared, opened, first, Activation.forgetRefs, Roots.set, other, ite_false] using atRoot
    exact Evaluator.Activation.write_other_root preparedMachine.native.valid destinationRoot rootNow (Ne.symm other)
      ((world.allocate_keeps h.native.wellFormed _ _ []).memory _ _ read) (.shared pointer)

end SubtreeProofs.Rust.SourceEval.Addressed
