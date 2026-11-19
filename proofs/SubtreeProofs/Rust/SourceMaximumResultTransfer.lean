module

public import SubtreeProofs.Rust.SourceMaximumCall
public import SubtreeProofs.Rust.SourceMoveAssignmentProvenance

/-! Move the public result option into its existing return local. The remaining
tuple mask contains exactly the updated table; its proven fresh owners survive
the partial move and actual guarded store. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Maximum

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def cleanupCode (index : Nat) : Code := (afterCall.drop index).foldr Control.Tree.step .ret

theorem result_transfer_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [5, 4, 1, 2] world active)
    (callee : Derived.Callees) (count : 7 ≤ active.count)
    {result : Option CommonEmbedding} {table : MemoTable}
    (output : active.state 3 = Slot.ofValue (Evaluator.encodeOutput result table))
    (above : LocalOwnersAbove before.memory.length world active 3)
    {root0 : Binding} (bound0 : active.roots 0 = some root0)
    (raw0 : world.memory[root0.address]? = some (.node .tuple 0 [])) (empty0 : active.state 0 = .empty) :
    ∃ final after,
      Calling.Prefix callee callers (cleanupCode 4) [.assign 0 (.use (.move (.field (.local 3) none 0)))]
        world active final after ∧
      OriginalLoanMachine before callers previous external [5, 4, 1, 2] final after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      after.state 0 = Slot.ofValue (encodeOption result) ∧ after.state 3 = Evaluator.headOptionHole table ∧
      LocalOwnersAbove before.memory.length final after 3 ∧
      (∀ slot, slot ∉ [0, 3] → (∀ value, active.state slot ≠ .shared value) → after.state slot = active.state slot) := by
  let code : Code := .step (.assign 0 (.use (.move (.field (.local 3) none 0)))) (cleanupCode 4)
  let prepared := active.forgetRefs code
  have machine := h.prepare code
  have sourceMask : prepared.state 3 = Slot.ofValue (Evaluator.encodeOutput result table) :=
    (h.prepare_closed_local code 3 (by decide)).trans output
  have remainingTyped : SlotTyped (Evaluator.headOptionHole table) (.tuple [.adt .optional, .adt .table]) :=
    .node (.tuple _) (.cons (.empty _) (.cons (ofValue_typed (table_typed table)) .nil))
  have closed : Borrow.Closed (.tuple [.adt .optional, .adt .table]) :=
    .tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))
  have source : SourceEval.expression prepared.state (.use (.move (.field (.local 3) none 0))) =
      some (encodeOption result, prepared.state.set 3 (Evaluator.headOptionHole table)) := by
    simp only [SourceEval.expression, SourceEval.operand, Partial.Locals.move, splitPlace,
      List.nil_append, sourceMask, Evaluator.head_option_take, bind, Option.bind]
  obtain ⟨cell, assigned, finalMachine⟩ := machine.assign_empty bound0 (by decide) raw0 source
    (by simp only [Partial.Locals.set, show (0 : Nat) ≠ 3 by decide, ite_false]
        exact LoanEnding.forget_empty code _ empty0)
    (machine.closed.set 3 remainingTyped closed)
    (by intro index member
        have different : index ≠ 3 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
        simp only [Partial.Locals.set, different, ite_false]; rfl)
    trivial (option_typed result) (.adt .optional)
  let final := world.write root0.address cell
  let after : Activation := {prepared with state := (prepared.state.set 3 (Evaluator.headOptionHole table)).set 0 (Slot.ofValue (encodeOption result))}
  have remaining := Derived.assign_operand_remaining_owner_provenance machine.native.valid
    machine.native.callersValid machine.native.wellFormed (other := 3) (by decide)
    (by change 3 < active.count; omega) (above.prepare_any code) assigned
  refine ⟨final, after, .cons (Calling.instruction_noncall_run (act := .assign 0 (.use (.move (.field (.local 3) none 0)))) assigned)
    (.nil _ _), finalMachine, rfl, rfl, rfl, ?_, ?_, remaining, ?_⟩
  · simp only [after, Partial.Locals.set, ite_true]
  · simp only [after, Partial.Locals.set, show (3 : Nat) ≠ 0 by decide, ite_false, ite_true]
  · intro slot outside unshared
    have h0 : slot ≠ 0 := by intro same; subst slot; simp at outside
    have h3 : slot ≠ 3 := by intro same; subst slot; simp at outside
    simp only [after, Partial.Locals.set, h0, h3, ite_false]
    exact LoanEnding.forget_unshared code _ unshared

end SubtreeProofs.Rust.SourceEval.Maximum
