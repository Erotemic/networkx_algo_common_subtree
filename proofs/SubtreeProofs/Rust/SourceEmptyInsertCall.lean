module

public import SubtreeProofs.Rust.SourceEmptyEmbeddingViews

/-! Construct the real insertion call from owned table and native shared views.
Native referent structure discharges the selected table-root move even when
query views alias table-owned data. Typed helper totality constructs the callee
and result store; original tuple loans survive the actual retained context. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def emptyInsertArgs : List Operand := [.move (.local 19), .move (.local 20), .move (.local 21), .move (.local 22)]

def emptyInsertMasks (state : State) : State := (((state.set 19 .empty).set 20 .empty).set 21 .empty).set 22 .empty

theorem empty_insert_arguments {state : State} (left right : BalancedWord) (table : MemoTable)
    (tableValue : state 19 = Slot.ofValue (encodeTable table))
    (leftValue : state 20 = .shared (encodeWord left)) (rightValue : state 21 = .shared (encodeWord right))
    (resultValue : state 22 = .shared (encodeResult emptyWitness)) :
    SourceEval.operands state emptyInsertArgs = some
      ([encodeTable table, .reference (encodeWord left), .reference (encodeWord right), .reference (encodeResult emptyWitness)], emptyInsertMasks state) := by
  simp [emptyInsertArgs, emptyInsertMasks, SourceEval.operands, SourceEval.operand, Partial.Locals.move,
    splitPlace, Slot.take, tableValue, leftValue, rightValue, resultValue, Partial.Locals.set,
    Slot.materialize_ofValue, Slot.materialize]

theorem empty_insert_call_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active) (data : MemoLoanState active.state)
    (closed : ClosedOutside [1, 2, 13, 20, 21, 22, 23] active.state)
    (left right : BalancedWord) (table : MemoTable)
    (tuple : active.state 13 = queryTuple left right) (tupleOrigin : LoanOrigin world active before.memory.length 13)
    (empty1 : active.state 1 = .empty) (empty2 : active.state 2 = .empty)
    (tableValue : active.state 19 = Slot.ofValue (encodeTable table))
    (leftValue : active.state 20 = .shared (encodeWord left)) (rightValue : active.state 21 = .shared (encodeWord right))
    (resultValue : active.state 22 = .shared (encodeResult emptyWitness)) (resultView : active.state 23 = .shared (encodeResult emptyWitness))
    {root18 : Binding} (bound18 : active.roots 18 = some root18)
    (empty18 : active.state 18 = .empty) (raw18 : world.memory[root18.address]? = some (.node .tuple 0 []))
    (count : 24 ≤ active.count) :
    ∃ minimumFuel minimumBudget final after cost,
      OriginalLoanMachine before callers previous external [1, 2, 13] final after ∧ after.roots = active.roots ∧ after.count = active.count ∧
      after.state 18 = Slot.ofValue (encodeTable (.Entry ⟨left, right, emptyWitness⟩ table)) ∧
      after.state 1 = .empty ∧ after.state 2 = .empty ∧ after.state 13 = queryTuple left right ∧
      (∀ slot ∈ [19, 20, 21, 22, 23], after.state slot = .empty) ∧
      (∀ slot, slot ∉ [18, 19, 20, 21, 22, 23] →
        (active.forgetRefs (emptyCode 18)).state slot = active.state slot → after.state slot = active.state slot) ∧
      (∀ slot binding, slot ≠ 18 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Derived.call (Recursive.original budget fuel) world (active.forgetRefs (emptyCode 18)) callers .insert emptyInsertArgs 18 = some (final, after, cost) ∧
        Calling.Prefix (Recursive.original budget fuel) callers (emptyCode 19) [.call .insert emptyInsertArgs 18] world active final after := by
  let observed := active.forgetRefs (emptyCode 18)
  have machine := h.prepare (emptyCode 18)
  have first : observed.state 19 = Slot.ofValue (encodeTable table) :=
    (LoanEnding.forget_closed (emptyCode 18) _ (by rw [tableValue]; exact ofValue_typed (table_typed table)) (.adt .table)).trans tableValue
  have second : observed.state 20 = .shared (encodeWord left) :=
    (Activation.forgetRefs_observed active (emptyCode 18) 20 (by decide +kernel)).trans leftValue
  have third : observed.state 21 = .shared (encodeWord right) :=
    (Activation.forgetRefs_observed active (emptyCode 18) 21 (by decide +kernel)).trans rightValue
  have fourth : observed.state 22 = .shared (encodeResult emptyWitness) :=
    (Activation.forgetRefs_observed active (emptyCode 18) 22 (by decide +kernel)).trans resultValue
  have ended23 : observed.state 23 = .empty := LoanEnding.forget_ended_shared (emptyCode 18) (List.range active.count)
    (by simp; omega) resultView (by decide +kernel)
  have observed1 : observed.state 1 = .empty := LoanEnding.forget_empty _ _ empty1
  have observed2 : observed.state 2 = .empty := LoanEnding.forget_empty _ _ empty2
  have observedTuple := prepare_queryTuple tuple (emptyCode 18)
  have arguments := empty_insert_arguments left right table first second third fourth
  have typed : SnapshotFieldsTyped [encodeTable table, .reference (encodeWord left), .reference (encodeWord right), .reference (encodeResult emptyWitness)]
      [.adt .table, .shared (.adt .word), .shared (.adt .word), .shared (.adt .embedding)] :=
    .cons (table_typed table) (.cons (.shared (word_typed left)) (.cons (.shared (word_typed right)) (.cons (.shared (result_typed emptyWitness)) .nil)))
  have output : Types.callOutput .insert [.adt .table, .shared (.adt .word), .shared (.adt .word), .shared (.adt .embedding)] = some (.adt .table) := by
    simp only [Types.callOutput, reduceCtorEq, ite_false, Types.inputs, SourceTypes.sameList_refl, ite_true, Types.output]
  have emptyMasks : (emptyInsertMasks observed.state) 18 = .empty := by
    simp only [emptyInsertMasks, Partial.Locals.set, show (18 : Nat) ≠ 22 by decide, show (18 : Nat) ≠ 21 by decide,
      show (18 : Nat) ≠ 20 by decide, show (18 : Nat) ≠ 19 by decide, ite_false]
    exact LoanEnding.forget_empty _ _ empty18
  have preparedData : MemoLoanState observed.state := data.prepare (emptyCode 18) _
  have moves : ∀ current suspended, Scanned world observed current → Callers world callers suspended →
      ∀ op ∈ emptyInsertArgs, Allowed world observed.roots (current.loans ++ suspended.reads) op := by
    intro current suspended scanned callerView op member
    simp only [emptyInsertArgs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact allowed_table_local machine preparedData scanned callerView first
    · obtain ⟨binding, hb⟩ := Activation.root_of_materialize machine.valid (value := .reference (encodeWord left)) (by rw [second]; simp only [Slot.materialize])
      exact machine.move_reference scanned callerView hb second
    · obtain ⟨binding, hb⟩ := Activation.root_of_materialize machine.valid (value := .reference (encodeWord right)) (by rw [third]; simp only [Slot.materialize])
      exact machine.move_reference scanned callerView hb third
    · obtain ⟨binding, hb⟩ := Activation.root_of_materialize machine.valid (value := .reference (encodeResult emptyWitness)) (by rw [fourth]; simp only [Slot.materialize])
      exact machine.move_reference scanned callerView hb fourth
  have loans := Derived.RootLoansAllowed.of_safe_preserved (slot := 18) (active := {observed with state := emptyInsertMasks observed.state})
    ((((machine.safe.clear 19).clear 20).clear 21).clear 22) raw18 (Or.inl rfl)
    h.previousCallers h.beforeWellFormed h.kept (h.fresh 18 root18 bound18)
  obtain ⟨minFuel, minBudget, final, after, cost, _, _, _, _, _, stable⟩ := Recursive.original_helper_call_stable
    machine.valid machine.callersValid machine.wellFormed machine.separate machine.ownerFrame machine.coverage
    .insert rfl emptyInsertArgs bound18 arguments emptyMasks typed output (.adt .table) moves loans
  let sufficient := max minFuel (MemoSource.insertDepth left right emptyWitness)
  have execute := (stable sufficient minBudget (Nat.le_max_left _ _) (by rfl)).1
  have source := (stable sufficient minBudget (Nat.le_max_left _ _) (by rfl)).2
  have ready := Derived.call_ready_from_values (callers := callers) machine.valid arguments typed output
  have callSpec := Derived.call_spec (Recursive.original_typed_respects minBudget sufficient) machine.valid machine.callersValid machine.wellFormed
    .insert emptyInsertArgs 18 ready execute
  have safe := LoanSafeState.call_closed (Types.original_run_typed sufficient) arguments
    ((((machine.safe.clear 19).clear 20).clear 21).clear 22) typed output (.adt .table) source
  have native := machine.advance_call (Recursive.original_typed_respects minBudget sufficient) (Recursive.original_owns minBudget sufficient)
    .insert emptyInsertArgs bound18 ready execute safe
  have roots := callSpec.2.2.2.1
  have countEq := callSpec.2.2.1
  obtain ⟨nativeCost, nativeRun, _⟩ := SourceEval.Helpers.insert_source table left right emptyWitness sufficient (Nat.le_max_right _ _)
  have resultState : after.state = (emptyInsertMasks observed.state).set 18 (Slot.ofValue (encodeTable (.Entry ⟨left, right, emptyWitness⟩ table))) := by
    change SourceEval.action (SourceEval.run Certificate.original.body sufficient) observed.state (.call .insert emptyInsertArgs 18) = some (after.state, cost) at source
    rw [SourceEval.action, arguments] at source
    simp only [bind, Option.bind] at source
    rw [nativeRun] at source
    exact (Prod.mk.inj (Option.some.inj source)).1.symm
  have value : after.state 18 = Slot.ofValue (encodeTable (.Entry ⟨left, right, emptyWitness⟩ table)) := by rw [resultState]; simp only [Partial.Locals.set, ite_true]
  have no1 : after.state 1 = .empty := by simpa [resultState, emptyInsertMasks, Partial.Locals.set] using observed1
  have no2 : after.state 2 = .empty := by simpa [resultState, emptyInsertMasks, Partial.Locals.set] using observed2
  have finalTuple : after.state 13 = queryTuple left right := by simpa [resultState, emptyInsertMasks, Partial.Locals.set] using observedTuple
  have emptyOthers : ∀ slot ∈ [19, 20, 21, 22, 23], after.state slot = .empty := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [resultState, emptyInsertMasks, Partial.Locals.set, ended23]
  have originalTuple : LoanOrigin final after before.memory.length 13 := by
    obtain ⟨r, represented, bound⟩ := tupleOrigin.prepare (emptyCode 18)
    have sameMask : (emptyInsertMasks observed.state) 13 = observed.state 13 := by simp [emptyInsertMasks, Partial.Locals.set]
    have kept := Derived.call_preserves_other_local (Recursive.original_typed_respects minBudget sufficient)
      machine.valid machine.callersValid machine.wellFormed .insert emptyInsertArgs 18 ready arguments sameMask (by decide)
      (by change 13 < active.count; omega) represented execute
    refine ⟨r, ?_, bound⟩
    rw [callSpec.2.1]
    apply (represented.transport kept).congr_at (congrFun roots 13)
    rw [resultState]
    simp [emptyInsertMasks, observed, Partial.Locals.set]
  have wide : ClosedOutside [1, 2, 13, 20, 21, 22, 23] after.state := by
    rw [resultState]
    exact (((((closed.forget (emptyCode 18) _).clear 19).clear 20).clear 21).clear 22).set 18
      (ofValue_typed (table_typed (.Entry ⟨left, right, emptyWitness⟩ table))) (.adt .table)
  have finalClosed : ClosedOutside [1, 2, 13] after.state := by
    intro slot outside
    by_cases temporary : slot ∈ [20, 21, 22, 23]
    · exact ⟨.u32, by rw [emptyOthers slot (by simpa using List.mem_cons_of_mem 19 temporary)]; exact .empty _, .u32⟩
    · exact wide slot (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside temporary ⊢; tauto)
  have original : OriginalLoanMachine before callers previous external [1, 2, 13] final after := by
    refine ⟨native, finalClosed, ?_, ?_⟩
    · intro slot member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · rw [no1]; simp only [Slot.dropWork]
      · rw [no2]; simp only [Slot.dropWork]
      · rw [finalTuple]; simp [queryTuple, Slot.dropWork, dropFields, DropWork.plus]
    · intro slot member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact LoanOrigin.of_closed native.valid before.memory.length 1 (by rw [no1]; exact .empty .u32) .u32
      · exact LoanOrigin.of_closed native.valid before.memory.length 2 (by rw [no2]; exact .empty .u32) .u32
      · exact originalTuple
  refine ⟨sufficient, minBudget, final, after, cost, original, roots, countEq, value, no1, no2, finalTuple, emptyOthers, ?_, ?_, ?_⟩
  · intro slot outside same
    rw [resultState]
    have eighteen : slot ≠ 18 := by intro eq; subst slot; simp at outside
    have nineteen : slot ≠ 19 := by intro eq; subst slot; simp at outside
    have twenty : slot ≠ 20 := by intro eq; subst slot; simp at outside
    have twentyOne : slot ≠ 21 := by intro eq; subst slot; simp at outside
    have twentyTwo : slot ≠ 22 := by intro eq; subst slot; simp at outside
    simpa only [emptyInsertMasks, Partial.Locals.set, eighteen, nineteen, twenty, twentyOne, twentyTwo, ite_false] using same
  · intro slot binding different hb raw memory
    have keeps := Derived.call_preserves_other_root (Recursive.original_typed_respects minBudget sufficient)
      machine.valid machine.callersValid machine.wellFormed .insert emptyInsertArgs 18 ready execute (other := slot) (target := binding) different hb
    exact keeps.reads binding.address (by simp) raw memory
  · intro fuel budget fuelBound budgetBound
    have actual := (stable fuel budget ((Nat.le_max_left _ _).trans fuelBound) budgetBound).1
    exact ⟨actual, .cons (Calling.instruction_call_run actual) (.nil _ _)⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
