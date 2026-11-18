module

public import SubtreeProofs.Rust.SourceEvaluatorLookupContinuation

/-! The complete common evaluator prefix reaches the actual lookup switch with
its native answer and checked scope: lookup temporaries are retired, table view
6 has ended, return storage is fresh and the other local roots are unchanged. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def commonPrefix : List Action := borrowPrefix ++ (.call .lookup lookupArgs 4 :: lookupRetire)

theorem actual_body_common_prefix : Certificate.original.body .evaluate =
    commonPrefix.foldr Control.Tree.step lookupSwitch := by
  rw [actual_body_lookup_prefix]
  simp only [commonPrefix, List.foldr_append, List.foldr_cons]
  rfl

structure LookupScope (initial : Activation) (left right : BalancedWord) (table : MemoTable)
    (world : World) (active : Activation) : Prop where
  inputs : InputLocals left right table active.state
  count : active.count = initial.count
  result : active.state 4 = Slot.ofValue (encodeOption (LookupEvents.lookup table left right).1)
  resultRoot : ∃ binding, active.roots 4 = some binding
  returnRoot : ∃ binding, active.roots 0 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])
  returnEmpty : active.state 0 = .empty
  viewRoot : ∃ binding pointer, active.roots 6 = some binding ∧ world.memory[binding.address]? = some (.shared pointer)
  viewEnded : active.state 6 = .empty
  retired : ∀ slot ∈ [5, 7, 8], active.roots slot = none
  otherRoots : ∀ slot, slot ∉ [0, 4, 5, 6, 7, 8] → active.roots slot = initial.roots slot

theorem common_prefix_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active)
    (count : 9 ≤ active.count) (left right : BalancedWord) (table : MemoTable)
    (inputs : InputLocals left right table active.state)
    (unbound : ∀ slot ∈ [0, 4, 5, 6, 7, 8], active.roots slot = none) :
    ∃ minimumFuel minimumBudget final after,
      LoanSafeMachine before callers previous external final after ∧ LookupScope active left right table final after ∧
      (QueryOrigins world active before.memory.length → QueryOrigins final after before.memory.length) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers lookupSwitch commonPrefix world active final after := by
  obtain ⟨middle, current, resultRoot, tableView, leftView, rightView, steps, machine, native, countEq,
    resultBinding, tableBinding, leftBinding, rightBinding, destination, empty, tableValue, leftValue, rightValue,
    sixEmpty, sixStorage, returnStorage, otherRoots, returnEmpty, beforeQueries⟩ :=
    borrow_prefix_complete h (Helpers.callee 0 0) count left right table inputs unbound
  obtain ⟨minFuel, minBudget, final, after, finalMachine, finalInputs, finalRoots, finalCount, finalValue,
    memoryKept, emptyKept, afterQueries, tail⟩ := lookup_continuation_complete machine left right table native
      resultBinding tableBinding leftBinding rightBinding destination empty tableValue leftValue rightValue
  have scope : LookupScope active left right table final after := by
    refine ⟨finalInputs, finalCount.trans countEq, finalValue, ?_, ?_, emptyKept 0 (by decide) returnEmpty, ?_, emptyKept 6 (by decide) sixEmpty, ?_, ?_⟩
    · exact ⟨resultRoot, by simpa [finalRoots, Roots.set] using resultBinding⟩
    · obtain ⟨binding, hb, memory⟩ := returnStorage
      exact ⟨binding, by simpa [finalRoots, Roots.set] using hb, memoryKept 0 binding (by decide) hb _ memory⟩
    · obtain ⟨binding, pointer, hb, memory⟩ := sixStorage
      exact ⟨binding, pointer, by simpa [finalRoots, Roots.set] using hb, memoryKept 6 binding (by decide) hb _ memory⟩
    · intro slot member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> simp [finalRoots, Roots.set]
    · intro slot member
      have five : slot ≠ 5 := by intro same; subst slot; simp at member
      have seven : slot ≠ 7 := by intro same; subst slot; simp at member
      have eight : slot ≠ 8 := by intro same; subst slot; simp at member
      simpa only [finalRoots, Roots.set, five, seven, eight, ite_false] using otherRoots slot member
  refine ⟨minFuel, minBudget, final, after, finalMachine, scope, fun queries => afterQueries (beforeQueries queries), ?_⟩
  intro fuel budget fuelBound budgetBound
  exact (steps.noncall_callee (Recursive.original budget fuel) (by decide +kernel)).append
    (tail fuel budget fuelBound budgetBound)

end SubtreeProofs.Rust.SourceEval.Evaluator
