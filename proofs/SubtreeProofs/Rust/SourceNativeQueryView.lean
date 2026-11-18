module

public import SubtreeProofs.Rust.SourceEvaluatorTableViews

/-! A fresh query-reference local is constructed through actual storage,
continuation-aware reference preparation and reborrowing. Existing roots retain
their cells; observed locals and empty masks retain their source values. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem query_view_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active) (callee : Derived.Callees) (suffix : Code)
    (destination query : Nat) (word : BalancedWord) (initialized : active.state query = .shared (encodeWord word))
    (bound : destination < active.count) (unbound : active.roots destination = none) :
    ∃ final after,
      Calling.Prefix callee callers suffix [.storageLive destination, .assign destination (.address (.deref (.local query)))]
        world active final after ∧ LoanSafeMachine before callers previous external final after ∧
      after.roots = active.roots.set destination (some ⟨world.memory.length, world.memory.length⟩) ∧
      after.count = active.count ∧ after.state destination = .shared (encodeWord word) ∧
      (∀ index, index ≠ destination →
        LoanEnding.endsBeforeObservation index (.step (.storageLive destination)
          (.step (.assign destination (.address (.deref (.local query)))) suffix)) = false →
        LoanEnding.endsBeforeObservation index (.step (.assign destination (.address (.deref (.local query)))) suffix) = false →
        after.state index = active.state index) ∧
      (∀ index, index ≠ destination → active.state index = .empty → after.state index = .empty) ∧
      (∀ index binding, active.roots index = some binding → ∀ cell,
        world.memory[binding.address]? = some cell → final.memory[binding.address]? = some cell) := by
  let next : Code := .step (.assign destination (.address (.deref (.local query)))) suffix
  let code : Code := .step (.storageLive destination) next
  have different : query ≠ destination := by
    intro same
    subst query
    obtain ⟨_, frame⟩ := h.valid.2
    have empty : active.state destination = .empty := by simpa only [unbound] using frame.slots destination
    rw [initialized] at empty
    cases empty
  have observed : LoanEnding.endsBeforeObservation query code = false := by
    simp [code, next, LoanEnding.endsBeforeObservation, LoanEnding.avoidsAction, LoanEnding.writes,
      LoanEnding.avoidsExpr, LoanEnding.avoidsPlace, splitPlace, Ne.symm different]
  have nextObserved : LoanEnding.endsBeforeObservation query next = false := by
    simp [next, LoanEnding.endsBeforeObservation, LoanEnding.avoidsAction, LoanEnding.avoidsExpr,
      LoanEnding.avoidsPlace, splitPlace]
  let first := active.forgetRefs code
  have firstMachine := h.prepare code
  let openedWorld := world.allocate (.stack first.frame destination world.memory.length) (.node .tuple 0 [])
  let opened : Activation := {first with roots := first.roots.set destination (some ⟨world.memory.length, world.memory.length⟩), state := first.state.set destination .empty}
  obtain ⟨openedRun, openedMachine⟩ := firstMachine.storageLive bound unbound
  change LoanSafeMachine before callers previous external openedWorld opened at openedMachine
  let prepared := opened.forgetRefs next
  have preparedMachine := openedMachine.prepare next
  have input : prepared.state query = .shared (encodeWord word) := by
    rw [Activation.forgetRefs_observed opened next query nextObserved]
    simp only [opened, Partial.Locals.set, different, ite_false]
    rw [Activation.forgetRefs_observed active code query observed]
    exact initialized
  have empty : prepared.state destination = .empty := by
    apply LoanEnding.forget_empty
    simp only [opened, Partial.Locals.set, ite_true]
  have source := address_shared_source input
  have safeValue : LoanSafe (Slot.ofValue (.reference (encodeWord word))) := by
    simpa only [Slot.ofValue] using LoanSafe.shared (NativeData.word word)
  have destinationBinding : prepared.roots destination = some ⟨world.memory.length, world.memory.length⟩ := by
    simp [prepared, opened, Roots.set, Activation.forgetRefs]
  obtain ⟨cell, assigned, finalMachine⟩ := preparedMachine.assign_empty destinationBinding (world.allocate_spec _ _).2.1 source
    empty preparedMachine.safe safeValue (by intros; trivial)
  let final := openedWorld.write world.memory.length cell
  let after : Activation := {prepared with state := prepared.state.set destination (Slot.ofValue (.reference (encodeWord word)))}
  refine ⟨final, after,
    .cons (Calling.instruction_noncall_run (act := .storageLive destination) openedRun)
      (.cons (Calling.instruction_noncall_run (act := .assign destination (.address (.deref (.local query)))) assigned) (.nil _ _)),
    finalMachine, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [after, Partial.Locals.set, ite_true, Slot.ofValue]
  · intro index different firstObserved secondObserved
    simp only [after, Partial.Locals.set, different, ite_false]
    rw [Activation.forgetRefs_observed opened next index secondObserved]
    simp only [opened, Partial.Locals.set, different, ite_false]
    rw [Activation.forgetRefs_observed active code index firstObserved]
  · intro index different wasEmpty
    simp only [after, Partial.Locals.set, different, ite_false]
    apply LoanEnding.forget_empty
    simp only [opened, Partial.Locals.set, different, ite_false]
    exact LoanEnding.forget_empty _ _ wasEmpty
  · intro index binding hb raw memory
    have different : index ≠ destination := by intro same; subst index; rw [unbound] at hb; cases hb
    have stillBound : prepared.roots index = some binding := by
      simpa only [prepared, opened, first, Roots.set, Activation.forgetRefs, different, ite_false] using hb
    have read : openedWorld.memory[binding.address]? = some raw :=
      (world.allocate_keeps h.wellFormed _ _ []).memory _ _ memory
    exact Activation.write_other_root preparedMachine.valid destinationBinding stillBound (Ne.symm different) read cell

end SubtreeProofs.Rust.SourceEval.Evaluator
