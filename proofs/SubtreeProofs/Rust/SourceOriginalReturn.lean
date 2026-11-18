module

public import SubtreeProofs.Rust.SourceOriginalRetirement
public import SubtreeProofs.Rust.SourceReturnTotality
public import SubtreeProofs.Rust.SourceCacheHitTransfer

/-! Construct the pinned parameter cleanup and checked return from any original
loan family once only return/parameter roots remain. Remaining reference masks
are retired through their actual fresh roots; no global alias ban is required. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem original_return_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active) (callee : Derived.Callees)
    {root0 root1 root2 root3 : Binding}
    (bound0 : active.roots 0 = some root0) (bound1 : active.roots 1 = some root1)
    (bound2 : active.roots 2 = some root2) (bound3 : active.roots 3 = some root3)
    (support : ∀ slot, slot ∉ [0, 1, 2, 3] → active.roots slot = none)
    (zeroQueries : ∀ slot ∈ [1, 2], (active.state slot).dropWork.boxes = 0)
    (empty3 : active.state 3 = .empty) {result : Option CommonEmbedding} {table : MemoTable}
    (output : active.state 0 = Slot.ofValue (encodeOutput result table)) :
    ∃ final after cell cost,
      Calling.exec callee callers returnResult world active = some (.returned final after (cell, encodeOutput result table), cost) ∧
      (∀ slot, after.state slot = .empty) ∧ after.RootsSeparate callers ∧
      (∀ slot binding, after.roots slot = some binding → before.memory.length ≤ binding.address) ∧
      Preserves before final previous.reads := by
  let actions : List Action := [.drop 3, .storageDead 3, .storageDead 2, .storageDead 1]
  have plan : RetirementPlan active.roots actions (((active.roots.set 3 none).set 2 none).set 1 none) :=
    .drop bound3 (.dead bound3 (.dead (binding := root2) (by simpa [Roots.set] using bound2)
      (.dead (binding := root1) (by simpa [Roots.set] using bound1) (.nil _))))
  have zero : ZeroRetirement actions active.state := by
    intro slot member
    simp [actions] at member
    rcases member with rfl | rfl | rfl
    · rw [empty3]; simp only [Slot.dropWork]
    · exact zeroQueries 2 (by simp)
    · exact zeroQueries 1 (by simp)
  obtain ⟨final, current, steps, machine, roots, count, memory⟩ := plan.complete_original callee .ret h rfl zero
  have current0 : current.roots 0 = some root0 := by simpa [roots, Roots.set] using bound0
  have output0 : current.state 0 = Slot.ofValue (encodeOutput result table) :=
    (steps.closed_local_same (index := 0) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [output]; exact ofValue_typed (encodeOutput_typed result table))
      (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (by decide +kernel) (by decide +kernel)).trans output
  have others : ∀ slot, slot ≠ 0 → current.state slot = .empty := by
    intro slot nonzero
    have unbound : current.roots slot = none := by
      rw [roots]
      by_cases one : slot = 1
      · subst slot; simp [Roots.set]
      by_cases two : slot = 2
      · subst slot; simp [Roots.set]
      by_cases three : slot = 3
      · subst slot; simp [Roots.set]
      simpa only [Roots.set, one, two, three, ite_false] using support slot (by simp [nonzero, one, two, three])
    obtain ⟨_, frame⟩ := machine.native.valid.2
    simpa only [unbound] using frame.slots slot
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
