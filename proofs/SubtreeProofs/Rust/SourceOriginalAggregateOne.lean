module

public import SubtreeProofs.Rust.SourceOriginalAggregate

/-! Construct a unary aggregate from an actual moved closed value. Original
loan origins discharge source and destination guards without constraining the
owned descendants of the value being wrapped. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem original_aggregate_one_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active) (callee : Derived.Callees) (suffix : Code)
    (source destination : Nat) (different : source ≠ destination)
    (sourceOutside : source ∉ exceptions) (outside : destination ∉ exceptions)
    (value : Value) (initialized : active.state source = Slot.ofValue value)
    (kind : Kind) (tag : Nat) {ty : Ty} (typed : SnapshotTyped (.node kind tag [value]) ty) (closed : Borrow.Closed ty)
    {binding : Binding} (root : active.roots destination = some binding)
    (raw : world.memory[binding.address]? = some (.node .tuple 0 [])) (empty : active.state destination = .empty) :
    ∃ final after,
      Calling.Prefix callee callers suffix [.assign destination (.aggregate kind tag [.move (.local source)])]
        world active final after ∧ OriginalLoanMachine before callers previous external exceptions final after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      after.state source = .empty ∧ after.state destination = Slot.ofValue (.node kind tag [value]) ∧
      (∀ index other, index ≠ destination → active.roots index = some other → ∀ cell,
        world.memory[other.address]? = some cell → final.memory[other.address]? = some cell) := by
  let rhs : Expr := .aggregate kind tag [.move (.local source)]
  let code : Code := .step (.assign destination rhs) suffix
  let prepared := active.forgetRefs code
  have machine := h.prepare code
  have valueP : prepared.state source = Slot.ofValue value := (h.prepare_closed_local _ source sourceOutside).trans initialized
  have sourceRun := Evaluator.aggregate_one_source (state := prepared.state) (slot := source)
    (by rw [valueP]; exact Slot.materialize_ofValue value) kind tag
  have emptyMasks : (prepared.state.set source .empty) destination = .empty := by
    simp only [Partial.Locals.set, Ne.symm different, ite_false]
    exact LoanEnding.forget_empty _ _ empty
  obtain ⟨cell, assigned, finalMachine⟩ := machine.assign_empty root outside raw sourceRun emptyMasks
    (machine.closed.clear source)
    (by intro index member
        have other : index ≠ source := by intro same; subst index; exact sourceOutside member
        simp only [Partial.Locals.set, other, ite_false]
        rfl)
    (by intro op member; have same := List.mem_singleton.mp member; subst op; trivial) typed closed
  let final := world.write binding.address cell
  let after : Activation := {prepared with state := (prepared.state.set source .empty).set destination (Slot.ofValue (.node kind tag [value]))}
  change OriginalLoanMachine before callers previous external exceptions final after at finalMachine
  refine ⟨final, after, .cons (Calling.instruction_noncall_run (act := .assign destination rhs) assigned) (.nil _ _),
    finalMachine, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp only [after, Partial.Locals.set, different, ite_false, ite_true]
  · simp only [after, Partial.Locals.set, ite_true]
  · intro index other notDestination bound rawCell memoryRead
    exact Evaluator.Activation.write_other_root machine.native.valid root bound (Ne.symm notDestination) memoryRead cell

end SubtreeProofs.Rust.SourceEval.Addressed
