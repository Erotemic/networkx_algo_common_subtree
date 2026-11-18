module

public import SubtreeProofs.Rust.SourceCacheMissProgram

/-! Construct the first three real miss instructions: drop the absent lookup
result and retire the ended table view and result storage. Native query inputs
and fresh return storage remain available for empty and recursive branches. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem InputLocals.prepare_miss {left right : BalancedWord} {table : MemoTable} {active : Activation}
    (h : InputLocals left right table active.state) (index : Nat) (bound : index ≤ 11) :
    InputLocals left right table (active.forgetRefs (missCode index)).state := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Activation.forgetRefs_observed active _ 1 (miss_observes_queries index bound 1 (by simp))]; exact h.left
  · rw [Activation.forgetRefs_observed active _ 2 (miss_observes_queries index bound 2 (by simp))]; exact h.right
  · exact (LoanEnding.forget_closed (missCode index) _ (by rw [h.table]; exact ofValue_typed (table_typed table))
      (.adt .table)).trans h.table

theorem miss_retire_complete {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : QueryMachine before callers previous external world active) (callee : Derived.Callees)
    {left right : BalancedWord} {table : MemoTable} (scope : LookupScope initial left right table world active)
    (miss : (LookupEvents.lookup table left right).1 = none) :
    ∃ final after,
      Calling.Prefix callee callers (missCode 3) (missSetupActions.take 3) world active final after ∧
      QueryMachine before callers previous external final after ∧ InputLocals left right table after.state ∧
      after.count = active.count ∧ final.memory = world.memory ∧
      after.roots 4 = none ∧ after.roots 6 = none ∧
      (∀ slot, slot ≠ 4 → slot ≠ 6 → after.roots slot = active.roots slot) ∧
      after.state 0 = .empty ∧
      (∃ root0, after.roots 0 = some root0 ∧ final.memory[root0.address]? = some (.node .tuple 0 [])) := by
  obtain ⟨root4, bound4⟩ := scope.resultRoot
  obtain ⟨root6, pointer6, bound6, raw6⟩ := scope.viewRoot
  let p0 := active.forgetRefs (missCode 0)
  have m0 := h.prepare (missCode 0)
  have i0 := scope.inputs.prepare_miss 0 (by decide)
  have absent : p0.state 4 = Slot.ofValue (encodeOption none) := by
    rw [h.prepare_closed_local _ 4 (by decide), scope.result, miss]
  obtain ⟨drop4, md4⟩ := m0.drop_zero bound4 (by rw [absent]; decide +kernel)
  let ad4 : Activation := {p0 with state := p0.state.set 4 .empty}
  change QueryMachine before callers previous external world ad4 at md4
  have id4 : InputLocals left right table ad4.state := i0.set 4 .empty (by decide)
  let p1 := ad4.forgetRefs (missCode 1)
  have m1 := md4.prepare (missCode 1)
  have i1 := id4.prepare_miss 1 (by decide)
  have zero6 : p1.state 6 = .empty := by
    rw [md4.prepare_closed_local _ 6 (by decide)]
    simp only [ad4, Partial.Locals.set, show (6 : Nat) ≠ 4 by decide, ite_false]
    exact (h.prepare_closed_local _ 6 (by decide)).trans scope.viewEnded
  obtain ⟨end6, me6⟩ := m1.storageDead bound6 (by rw [zero6]; decide +kernel)
  let w6 := world.retire [root6.address]
  let ae6 : Activation := {p1 with roots := p1.roots.set 6 none, state := p1.state.set 6 .empty}
  change QueryMachine before callers previous external w6 ae6 at me6
  have ie6 : InputLocals left right table ae6.state := i1.set 6 .empty (by decide)
  let p2 := ae6.forgetRefs (missCode 2)
  have m2 := me6.prepare (missCode 2)
  have i2 := ie6.prepare_miss 2 (by decide)
  have bound4p2 : p2.roots 4 = some root4 := by
    simpa only [p2, ae6, p1, ad4, p0, Activation.forgetRefs, Roots.set, show (4 : Nat) ≠ 6 by decide, ite_false] using bound4
  have zero4 : p2.state 4 = .empty := by
    rw [me6.prepare_closed_local _ 4 (by decide)]
    simp only [ae6, Partial.Locals.set, show (4 : Nat) ≠ 6 by decide, ite_false]
    rw [md4.prepare_closed_local _ 4 (by decide)]
    simp only [ad4, Partial.Locals.set, ite_true]
  obtain ⟨end4, me4⟩ := m2.storageDead bound4p2 (by rw [zero4]; decide +kernel)
  let final := w6.retire [root4.address]
  let after : Activation := {p2 with roots := p2.roots.set 4 none, state := p2.state.set 4 .empty}
  change QueryMachine before callers previous external final after at me4
  have steps : Calling.Prefix callee callers (missCode 3) (missSetupActions.take 3) world active final after :=
    .cons (Calling.instruction_noncall_run (act := .drop 4) drop4)
      (.cons (Calling.instruction_noncall_run (act := .storageDead 6) end6)
        (.cons (Calling.instruction_noncall_run (act := .storageDead 4) end4) (.nil _ _)))
  refine ⟨final, after, steps, me4, i2.set 4 .empty (by decide), rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [after, Roots.set, ite_true]
  · simp [after, p2, ae6, Roots.set, Activation.forgetRefs]
  · intro slot four six
    simp only [after, p2, ae6, p1, ad4, p0, Activation.forgetRefs, Roots.set, four, six, ite_false]
  · exact (steps.closed_local_same (index := 0) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.returnEmpty]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans scope.returnEmpty
  · obtain ⟨root0, bound0, raw0⟩ := scope.returnRoot
    refine ⟨root0, ?_, raw0⟩
    simpa [after, p2, ae6, p1, ad4, p0, Roots.set, Activation.forgetRefs] using bound0

end SubtreeProofs.Rust.SourceEval.Evaluator
