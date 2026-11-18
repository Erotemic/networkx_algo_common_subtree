module

public import SubtreeProofs.Rust.SourceCacheHitReturn

/-! Construct the actual lookup switch, whole hit branch and return join from
its independently derived native lookup result. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem hit_continuation_complete {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : QueryMachine before callers previous external world active) (callee : Derived.Callees)
    {left right : BalancedWord} {table : MemoTable} (scope : LookupScope initial left right table world active)
    (unbound : ∀ slot, slot ∉ [1, 2, 3] → initial.roots slot = none) (count : 13 ≤ active.count)
    (result : CommonEmbedding) (hit : (LookupEvents.lookup table left right).1 = some result) :
    ∃ final after cell cost,
      Calling.exec callee callers lookupSwitch world active = some (.returned final after (cell, encodeOutput (some result) table), cost) ∧
      (∀ slot, after.state slot = .empty) ∧ after.RootsSeparate callers ∧
      (∀ slot binding, after.roots slot = some binding → before.memory.length ≤ binding.address) ∧
      Preserves before final previous.reads := by
  obtain ⟨root0, bound0, raw0⟩ := scope.returnRoot
  obtain ⟨root1, bound1⟩ := Activation.root_of_materialize h.native.valid (value := .reference (encodeWord left))
    (by rw [scope.inputs.left]; simp only [Slot.materialize])
  obtain ⟨root2, bound2⟩ := Activation.root_of_materialize h.native.valid (value := .reference (encodeWord right))
    (by rw [scope.inputs.right]; simp only [Slot.materialize])
  obtain ⟨root3, bound3⟩ := Activation.root_of_materialize h.native.valid
    (by rw [scope.inputs.table]; exact Slot.materialize_ofValue _)
  obtain ⟨middle, current, steps, machine, countAfter, keptRoots, support, output, empty3⟩ :=
    hit_branch_complete h callee scope unbound count result hit
  obtain ⟨final, after, cell, last, returnRun, empty, separate, fresh, kept⟩ := hit_return_complete machine callee
    (by rw [keptRoots 0 (by simp)]; exact bound0) (by rw [keptRoots 1 (by simp)]; exact bound1)
    (by rw [keptRoots 2 (by simp)]; exact bound2) (by rw [keptRoots 3 (by simp)]; exact bound3) support empty3 output
  obtain ⟨branchCost, branchRun⟩ := steps.exec (Calling.exec_done callee callers middle current)
  have branch : Calling.exec callee callers cacheHit world active = some (.next middle current, branchCost) := by
    rw [cacheHit_actions]; exact branchRun
  have observed := (lookup_switch_native h.native left right table scope).1
  rw [hit] at observed
  refine ⟨final, after, cell, ((Cost.local (1 + (Scrutinee.discriminant (.local 4)).weight)).plus branchCost).plus last, ?_, empty, separate, fresh, kept⟩
  rw [lookupSwitch, Calling.exec_switch, observed]
  simp only [lookupKey, Control.selectSource, Control.selectIndex, ite_true, branch, bind, Option.bind]
  rw [returnRun]

end SubtreeProofs.Rust.SourceEval.Evaluator
