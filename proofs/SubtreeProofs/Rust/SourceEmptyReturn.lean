module

public import SubtreeProofs.Rust.SourceEmptyReturnPacking
public import SubtreeProofs.Rust.SourceReturnTotality

/-! Construct the thirteen actual empty-branch cleanup instructions and the
checked return. The copied query tuple is nonowning even when its references
point into the transferred native table. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def emptyCleanupSlots : List Nat := [26, 24, 18, 16, 13, 3, 2, 1]

def emptyCleanupRoots (roots : Roots) : Roots :=
  ((((((((roots.set 26 none).set 24 none).set 18 none).set 16 none).set 13 none).set 3 none).set 2 none).set 1 none)

theorem empty_cleanup_return_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [1, 2, 13] world active) (callee : Derived.Callees)
    {root0 : Binding} (bound0 : active.roots 0 = some root0)
    (bound : ∀ slot ∈ emptyCleanupSlots, ∃ binding, active.roots slot = some binding)
    (zero : ∀ slot ∈ emptyCleanupSlots, (active.state slot).dropWork.boxes = 0)
    (support : ∀ slot, slot ≠ 0 → slot ∉ emptyCleanupSlots → active.roots slot = none)
    {result : Option CommonEmbedding} {table : MemoTable}
    (output : active.state 0 = Slot.ofValue (encodeOutput result table)) :
    ∃ final after cell cost,
      Calling.exec callee callers (emptyCode 34) world active = some (.returned final after (cell, encodeOutput result table), cost) ∧
      (∀ slot, after.state slot = .empty) ∧ after.RootsSeparate callers ∧
      (∀ slot binding, after.roots slot = some binding → before.memory.length ≤ binding.address) ∧
      Preserves before final previous.reads := by
  obtain ⟨root26, bound26⟩ := bound 26 (by simp [emptyCleanupSlots])
  obtain ⟨root24, bound24⟩ := bound 24 (by simp [emptyCleanupSlots])
  obtain ⟨root18, bound18⟩ := bound 18 (by simp [emptyCleanupSlots])
  obtain ⟨root16, bound16⟩ := bound 16 (by simp [emptyCleanupSlots])
  obtain ⟨root13, bound13⟩ := bound 13 (by simp [emptyCleanupSlots])
  obtain ⟨root3, bound3⟩ := bound 3 (by simp [emptyCleanupSlots])
  obtain ⟨root2, bound2⟩ := bound 2 (by simp [emptyCleanupSlots])
  obtain ⟨root1, bound1⟩ := bound 1 (by simp [emptyCleanupSlots])
  have plan : RetirementPlan active.roots (emptyActions.drop 34) (emptyCleanupRoots active.roots) := by
    refine .drop bound26 (.dead bound26 (.drop (binding := root24) ?_ (.dead (binding := root24) ?_
      (.drop (binding := root18) ?_ (.dead (binding := root18) ?_
        (.drop (binding := root16) ?_ (.dead (binding := root16) ?_
          (.dead (binding := root13) ?_ (.drop (binding := root3) ?_ (.dead (binding := root3) ?_
            (.dead (binding := root2) ?_ (.dead (binding := root1) ?_ (.nil _)))))))))))))
    all_goals first
      | simpa [Roots.set] using bound24
      | simpa [Roots.set] using bound18
      | simpa [Roots.set] using bound16
      | simpa [Roots.set] using bound13
      | simpa [Roots.set] using bound3
      | simpa [Roots.set] using bound2
      | simpa [Roots.set] using bound1
  have work : ZeroRetirement (emptyActions.drop 34) active.state := by
    intro slot member
    apply zero slot
    simp [emptyActions] at member
    simp only [emptyCleanupSlots, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  obtain ⟨final, current, steps, machine, roots, count, memory⟩ := plan.complete_original callee .ret h rfl work
  have current0 : current.roots 0 = some root0 := by simpa [roots, emptyCleanupRoots, Roots.set] using bound0
  have output0 : current.state 0 = Slot.ofValue (encodeOutput result table) :=
    (steps.closed_local_same (index := 0) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [output]; exact ofValue_typed (encodeOutput_typed result table))
      (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (by decide +kernel) (by decide +kernel)).trans output
  have unbound : ∀ slot, slot ≠ 0 → current.roots slot = none := by
    intro slot nonzero
    rw [roots]
    by_cases member : slot ∈ emptyCleanupSlots
    · simp only [emptyCleanupSlots, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [emptyCleanupRoots, Roots.set]
    · have outside : slot ≠ 26 ∧ slot ≠ 24 ∧ slot ≠ 18 ∧ slot ≠ 16 ∧ slot ≠ 13 ∧ slot ≠ 3 ∧ slot ≠ 2 ∧ slot ≠ 1 := by
        simpa [emptyCleanupSlots] using member
      simpa only [emptyCleanupRoots, Roots.set, outside.1, outside.2.1, outside.2.2.1, outside.2.2.2.1,
        outside.2.2.2.2.1, outside.2.2.2.2.2.1, outside.2.2.2.2.2.2.1, outside.2.2.2.2.2.2.2, ite_false] using support slot nonzero member
  have others : ∀ slot, slot ≠ 0 → current.state slot = .empty := by
    intro slot nonzero
    obtain ⟨_, frame⟩ := machine.native.valid.2
    simpa only [unbound slot nonzero] using frame.slots slot
  have closed : ClosedState current.state := by
    intro slot
    by_cases isZero : slot = 0
    · subst slot
      exact ⟨_, by rw [output0]; exact ofValue_typed (encodeOutput_typed result table),
        .tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))⟩
    · exact ⟨.u32, by rw [others slot isZero]; exact .empty _, .u32⟩
  have loans := Derived.ReturnLoansAllowed.of_closed_preserved (fun slot _ => closed slot) h.native.previousCallers
    h.native.beforeWellFormed machine.native.kept (machine.native.fresh 0 root0 current0)
  obtain ⟨cell, run⟩ := Derived.returnValue_complete machine.native.valid machine.native.callersValid machine.native.separate
    machine.native.ownerFrame current0 (by rw [output0]; exact Slot.materialize_ofValue _) loans
  obtain ⟨cost, whole⟩ := steps.exec run
  refine ⟨final, {current with state := current.state.set 0 .empty}, cell, cost, whole, ?_, machine.native.separate,
    machine.native.fresh, machine.native.kept⟩
  intro slot
  by_cases isZero : slot = 0
  · subst slot; simp only [Partial.Locals.set, ite_true]
  · simpa only [Partial.Locals.set, isZero, ite_false] using others slot isZero

end SubtreeProofs.Rust.SourceEval.Evaluator
