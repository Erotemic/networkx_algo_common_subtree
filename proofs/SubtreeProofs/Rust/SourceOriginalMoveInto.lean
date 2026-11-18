module

public import SubtreeProofs.Rust.SourceOriginalProjectView
public import SubtreeProofs.Rust.SourcePrefixCallPreservation

/-! Construct a closed native move into an existing empty bound local. Actual
original loan origins discharge the selected source/root and store guards. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem original_move_into_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active) (callee : Derived.Callees) (suffix : Code)
    {source destination : Nat} (sourceOutside : source ∉ exceptions) (outside : destination ∉ exceptions) (different : source ≠ destination)
    {value : Value} {ty : Ty} (initialized : active.state source = Slot.ofValue value)
    (typed : SnapshotTyped value ty) (closed : Borrow.Closed ty)
    {binding : Binding} (root : active.roots destination = some binding)
    (raw : world.memory[binding.address]? = some (.node .tuple 0 [])) (empty : active.state destination = .empty) :
    ∃ final after,
      Calling.Prefix callee callers suffix [.assign destination (.use (.move (.local source)))] world active final after ∧
      OriginalLoanMachine before callers previous external exceptions final after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      after.state source = .empty ∧ after.state destination = Slot.ofValue value ∧
      (∀ index binding, index ≠ destination → active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  let code : Code := .step (.assign destination (.use (.move (.local source)))) suffix
  let prepared := active.forgetRefs code
  have machine := h.prepare code
  have sourceValue : prepared.state source = Slot.ofValue value :=
    (h.prepare_closed_local code source sourceOutside).trans initialized
  have emptyDestination : (prepared.state.set source .empty) destination = .empty := by
    simp only [Partial.Locals.set, Ne.symm different, ite_false]
    exact (h.prepare_closed_local code destination outside).trans empty
  obtain ⟨cell, run, afterMachine⟩ := machine.assign_empty root outside raw
    (Evaluator.use_local_source (state := prepared.state) (slot := source) (by rw [sourceValue]; exact Slot.materialize_ofValue _))
    emptyDestination (machine.closed.clear source)
    (by intro index member
        have other : index ≠ source := by intro same; subst index; exact sourceOutside member
        simp only [Partial.Locals.set, other, ite_false, prepared]) trivial typed closed
  let final := world.write binding.address cell
  let after : Activation := {prepared with state := (prepared.state.set source .empty).set destination (Slot.ofValue value)}
  refine ⟨final, after, .cons (Calling.instruction_noncall_run (act := .assign destination (.use (.move (.local source)))) run) (.nil _ _),
    afterMachine, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp only [after, Partial.Locals.set, different, ite_false, ite_true]
  · simp only [after, Partial.Locals.set, ite_true]
  · intro index other notDestination atRoot rawCell memoryRead
    exact Evaluator.Activation.write_other_root machine.native.valid root atRoot (Ne.symm notDestination) memoryRead cell

end SubtreeProofs.Rust.SourceEval.Addressed
