module

public import SubtreeProofs.Rust.SourceOriginalMoveView

/-! Aggregate two moved closed values into existing empty actual storage. The
independent constructor type and actual argument masks remain explicit; complete
owners, original query loans and untouched root bytes are transferred safely. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem original_aggregate_two_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active) (callee : Derived.Callees) (suffix : Code)
    (first second destination : Nat) (different : first ≠ second) (df : destination ≠ first) (ds : destination ≠ second)
    (firstOutside : first ∉ exceptions) (secondOutside : second ∉ exceptions) (outside : destination ∉ exceptions)
    (left right : Value) (firstValue : active.state first = Slot.ofValue left) (secondValue : active.state second = Slot.ofValue right)
    (kind : Kind) (tag : Nat) {ty : Ty} (typed : SnapshotTyped (.node kind tag [left, right]) ty) (closed : Borrow.Closed ty)
    {binding : Binding} (root : active.roots destination = some binding)
    (raw : world.memory[binding.address]? = some (.node .tuple 0 [])) (empty : active.state destination = .empty) :
    ∃ final after,
      Calling.Prefix callee callers suffix [.assign destination (.aggregate kind tag [.move (.local first), .move (.local second)])]
        world active final after ∧ OriginalLoanMachine before callers previous external exceptions final after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      after.state first = .empty ∧ after.state second = .empty ∧
      after.state destination = Slot.ofValue (.node kind tag [left, right]) ∧
      (∀ slot, slot ≠ first → slot ≠ second → slot ≠ destination → ∀ otherTy,
        SlotTyped (active.state slot) otherTy → Borrow.Closed otherTy → after.state slot = active.state slot) ∧
      (∀ index other, index ≠ destination → active.roots index = some other → ∀ cell,
        world.memory[other.address]? = some cell → final.memory[other.address]? = some cell) := by
  let rhs : Expr := .aggregate kind tag [.move (.local first), .move (.local second)]
  let code : SourceEval.Code := .step (.assign destination rhs) suffix
  let prepared := active.forgetRefs code
  have machine := h.prepare code
  have firstP : prepared.state first = Slot.ofValue left := (h.prepare_closed_local _ first firstOutside).trans firstValue
  have secondP : prepared.state second = Slot.ofValue right := (h.prepare_closed_local _ second secondOutside).trans secondValue
  have source := Evaluator.aggregate_two_source (state := prepared.state) (first := first) (second := second)
    (by rw [firstP]; exact Slot.materialize_ofValue left) (by rw [secondP]; exact Slot.materialize_ofValue right) (Ne.symm different) kind tag
  have emptyMasks : ((prepared.state.set first .empty).set second .empty) destination = .empty := by
    simp only [Partial.Locals.set, df, ds, ite_false]
    exact LoanEnding.forget_empty _ _ empty
  obtain ⟨cell, assigned, finalMachine⟩ := machine.assign_empty root outside raw source emptyMasks
    ((machine.closed.clear first).clear second)
    (by intro index member
        have notFirst : index ≠ first := by intro same; subst index; exact firstOutside member
        have notSecond : index ≠ second := by intro same; subst index; exact secondOutside member
        simp only [Partial.Locals.set, notFirst, notSecond, ite_false]
        rfl)
    (by intro op member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> trivial) typed closed
  let final := world.write binding.address cell
  let after : Activation := {prepared with state := ((prepared.state.set first .empty).set second .empty).set destination (Slot.ofValue (.node kind tag [left, right]))}
  change OriginalLoanMachine before callers previous external exceptions final after at finalMachine
  refine ⟨final, after, .cons (Calling.instruction_noncall_run (act := .assign destination rhs) assigned) (.nil _ _),
    finalMachine, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [after, Partial.Locals.set, Ne.symm df, different, ite_false, ite_true]
  · simp only [after, Partial.Locals.set, Ne.symm ds, ite_false, ite_true]
  · simp only [after, Partial.Locals.set, ite_true]
  · intro slot notFirst notSecond notDestination otherTy otherTyped otherClosed
    simp only [after, Partial.Locals.set, notFirst, notSecond, notDestination, ite_false]
    exact LoanEnding.forget_closed _ _ otherTyped otherClosed
  · intro index other notDestination bound value memoryRead
    exact Evaluator.Activation.write_other_root machine.native.valid root bound (Ne.symm notDestination) memoryRead cell

end SubtreeProofs.Rust.SourceEval.Addressed
