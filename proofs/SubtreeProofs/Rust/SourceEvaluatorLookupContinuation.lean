module

public import SubtreeProofs.Rust.SourceEvaluatorLookupRetirement
public import SubtreeProofs.Rust.SourceQueryCallPreservation

/-! Construct lookup and retirement together, recovering the independent native
lookup answer from the existing source theorem at sufficient fuel. All moves,
result storage and temporary-root retirement are derived before execution. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem lookup_continuation_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active)
    (left right : BalancedWord) (table : MemoTable) (inputs : InputLocals left right table active.state)
    {resultRoot tableView leftView rightView : Binding}
    (resultBinding : active.roots 4 = some resultRoot) (tableBinding : active.roots 5 = some tableView)
    (leftBinding : active.roots 7 = some leftView) (rightBinding : active.roots 8 = some rightView)
    (destination : world.memory[resultRoot.address]? = some (.node .tuple 0 []))
    (empty : active.state 4 = .empty) (tableValue : active.state 5 = .shared (encodeTable table))
    (leftValue : active.state 7 = .shared (encodeWord left)) (rightValue : active.state 8 = .shared (encodeWord right)) :
    ∃ minimumFuel minimumBudget final after,
      LoanSafeMachine before callers previous external final after ∧ InputLocals left right table after.state ∧
      after.roots = ((active.roots.set 8 none).set 7 none).set 5 none ∧ after.count = active.count ∧
      after.state 4 = Slot.ofValue (encodeOption (LookupEvents.lookup table left right).1) ∧
      (∀ other target, other ≠ 4 → active.roots other = some target → ∀ cell,
        world.memory[target.address]? = some cell → final.memory[target.address]? = some cell) ∧
      (∀ index, index ∉ [4, 5, 7, 8] → active.state index = .empty → after.state index = .empty) ∧
      (QueryOrigins world active before.memory.length → QueryOrigins final after before.memory.length) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers lookupSwitch
          (.call .lookup lookupArgs 4 :: lookupRetire) world active final after := by
  let observed := active.forgetRefs lookupSuffix
  have machine := h.prepare lookupSuffix
  have observedInputs : InputLocals left right table observed.state := inputs.prepare 10 (by decide)
  have first : observed.state 5 = .shared (encodeTable table) := by
    rw [Activation.forgetRefs_observed active lookupSuffix 5 (by decide +kernel)]; exact tableValue
  have second : observed.state 7 = .shared (encodeWord left) := by
    rw [Activation.forgetRefs_observed active lookupSuffix 7 (by decide +kernel)]; exact leftValue
  have third : observed.state 8 = .shared (encodeWord right) := by
    rw [Activation.forgetRefs_observed active lookupSuffix 8 (by decide +kernel)]; exact rightValue
  have arguments := lookup_arguments left right table first second third
  have typed : SnapshotFieldsTyped [.reference (encodeTable table), .reference (encodeWord left), .reference (encodeWord right)]
      [.shared (.adt .table), .shared (.adt .word), .shared (.adt .word)] :=
    .cons (.shared (table_typed table)) (.cons (.shared (word_typed left)) (.cons (.shared (word_typed right)) .nil))
  have output : Types.callOutput .lookup [.shared (.adt .table), .shared (.adt .word), .shared (.adt .word)] = some (.adt .optional) := by
    simp only [Types.callOutput, reduceCtorEq, ite_false, Types.inputs, SourceTypes.sameList_refl, ite_true, Types.output]
  have ready := Derived.call_ready_from_values (callers := callers) machine.valid arguments typed output
  obtain ⟨minFuel, minBudget, returned, result, cost, _, _, _, _, _, stable⟩ :=
    lookup_call_complete h left right table resultBinding tableBinding leftBinding rightBinding
      destination empty tableValue leftValue rightValue
  let sufficient := max minFuel (lookupDepth table left right)
  have execute := (stable sufficient minBudget (Nat.le_max_left _ _) (by omega)).1
  have source := (stable sufficient minBudget (Nat.le_max_left _ _) (by omega)).2
  have resultMachine := lookup_call_machine minBudget sufficient h left right table resultBinding tableValue leftValue rightValue execute
  have callSpec := Derived.call_spec (Recursive.original_typed_respects minBudget sufficient) machine.valid
    machine.callersValid machine.wellFormed .lookup lookupArgs 4 ready execute
  have roots := callSpec.2.2.2.1
  have count := callSpec.2.2.1
  obtain ⟨nativeCost, nativeRun, _⟩ := SourceEval.Helpers.lookup_source table left right sufficient (Nat.le_max_right _ _)
  have resultState : result.state = (((observed.state.set 5 .empty).set 7 .empty).set 8 .empty).set 4
      (Slot.ofValue (encodeOption (LookupEvents.lookup table left right).1)) := by
    change SourceEval.action (SourceEval.run Certificate.original.body sufficient) observed.state
      (.call .lookup lookupArgs 4) = some (result.state, cost) at source
    rw [SourceEval.action, arguments] at source
    simp only [bind, Option.bind] at source
    rw [nativeRun] at source
    exact (Prod.mk.inj (Option.some.inj source)).1.symm
  have resultInputs : InputLocals left right table result.state := by
    rw [resultState]
    exact (((observedInputs.set 5 .empty (by simp)).set 7 .empty (by simp)).set 8 .empty (by simp)).set 4 _ (by simp)
  have tableRoot : result.roots 5 = some tableView := by rw [roots]; exact tableBinding
  have leftRoot : result.roots 7 = some leftView := by rw [roots]; exact leftBinding
  have rightRoot : result.roots 8 = some rightView := by rw [roots]; exact rightBinding
  obtain ⟨tablePointer, tableMemory⟩ := h.shared_root tableBinding tableValue
  obtain ⟨leftPointer, leftMemory⟩ := h.shared_root leftBinding leftValue
  obtain ⟨rightPointer, rightMemory⟩ := h.shared_root rightBinding rightValue
  have keeps := fun other target different hb =>
    Derived.call_preserves_other_root (Recursive.original_typed_respects minBudget sufficient)
      machine.valid machine.callersValid machine.wellFormed .lookup lookupArgs 4 ready execute
      (other := other) (target := target) different hb
  have tableRead := (keeps 5 tableView (by decide) tableBinding).reads _ (by simp) _ tableMemory
  have leftRead := (keeps 7 leftView (by decide) leftBinding).reads _ (by simp) _ leftMemory
  have rightRead := (keeps 8 rightView (by decide) rightBinding).reads _ (by simp) _ rightMemory
  obtain ⟨final, after, retire, finalMachine, finalInputs, finalRoots, finalCount, finalValue, finalMemory, finalEmpty, retireQueries⟩ :=
    retire_lookup_complete resultMachine (Helpers.callee 0 0) left right table resultInputs tableRoot leftRoot rightRoot
      tableRead leftRead rightRead
      (by rw [resultState]; simp [Partial.Locals.set])
      (by rw [resultState]; simp [Partial.Locals.set])
      (by rw [resultState]; simp [Partial.Locals.set])
  refine ⟨sufficient, minBudget, final, after, finalMachine, finalInputs, ?_, finalCount.trans count, ?_, ?_, ?_, ?_, ?_⟩
  · rw [finalRoots, roots]; rfl
  · rw [finalValue, resultState]; simp only [Partial.Locals.set, ite_true]
  · intro other target different hb cell memory
    rw [finalMemory]
    exact (keeps other target different hb).reads _ (by simp) _ memory
  · intro index member empty
    have four : index ≠ 4 := by intro same; subst index; simp at member
    have five : index ≠ 5 := by intro same; subst index; simp at member
    have seven : index ≠ 7 := by intro same; subst index; simp at member
    have eight : index ≠ 8 := by intro same; subst index; simp at member
    apply finalEmpty index (by simp [five, seven, eight])
    rw [resultState]
    simp only [Partial.Locals.set, four, five, seven, eight, ite_false]
    exact LoanEnding.forget_empty _ _ empty
  · intro queries
    have atResult : QueryOrigins returned result before.memory.length := by
      intro index member
      obtain ⟨r, represented, bound⟩ := (queries.prepare lookupSuffix) index member
      have four : index ≠ 4 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> decide
      have maskSame : (((observed.state.set 5 .empty).set 7 .empty).set 8 .empty) index = observed.state index := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> simp [Partial.Locals.set]
      have eightBound : 8 < active.count := by
        by_contra no
        have noneRoot := h.valid.1 8 (by omega)
        rw [rightBinding] at noneRoot
        cases noneRoot
      have indexBound : index < observed.count := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> change _ < active.count <;> omega
      have kept := Derived.call_preserves_other_local (Recursive.original_typed_respects minBudget sufficient)
        machine.valid machine.callersValid machine.wellFormed .lookup lookupArgs 4 ready arguments maskSame four indexBound represented execute
      refine ⟨r, ?_, bound⟩
      rw [callSpec.2.1]
      apply (represented.transport kept).congr_at (congrFun roots index)
      rw [resultState]
      simpa only [Partial.Locals.set, four, ite_false] using maskSame
    exact retireQueries atResult
  · intro fuel budget fuelBound budgetBound
    have tail := retire.noncall_callee (Recursive.original budget fuel) (by decide +kernel)
    exact .cons (Calling.instruction_call_run (stable fuel budget ((Nat.le_max_left _ _).trans fuelBound) budgetBound).1) tail

end SubtreeProofs.Rust.SourceEval.Evaluator
