module

public import SubtreeProofs.Rust.SourcePairInsertViews

/-! Construct the actual parent insertion call with arbitrary native selected
witness and table. Original loans and fresh embedding views jointly discharge
table permission. The call restores the original loan family and preserves
selected/owned-query provenance; transferred table owners remain unrestricted. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def pairInsertArgs : List Operand := [.move (.local 105), .move (.local 106), .move (.local 107), .move (.local 108)]

def pairInsertMasks (state : State) : State := (((state.set 105 .empty).set 106 .empty).set 107 .empty).set 108 .empty

theorem pair_insert_arguments {state : State} (left right : BalancedWord) (table : MemoTable) (result : CommonEmbedding)
    (tableValue : state 105 = Slot.ofValue (encodeTable table))
    (leftValue : state 106 = .shared (encodeWord left)) (rightValue : state 107 = .shared (encodeWord right))
    (resultValue : state 108 = .shared (encodeResult result)) :
    SourceEval.operands state pairInsertArgs = some
      ([encodeTable table, .reference (encodeWord left), .reference (encodeWord right), .reference (encodeResult result)], pairInsertMasks state) := by
  simp [pairInsertArgs, pairInsertMasks, SourceEval.operands, SourceEval.operand, Partial.Locals.move,
    splitPlace, Slot.take, tableValue, leftValue, rightValue, resultValue, Partial.Locals.set,
    Slot.materialize_ofValue, Slot.materialize]

theorem pair_insert_call_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active)
    (data : MemoLoanOrigins before.memory.length world active)
    (closed : ClosedOutside [108, 109, 107, 106, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] active.state)
    (origins : ∀ slot ∈ [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13], LoanOrigin world active before.memory.length slot)
    (zero : ∀ slot ∈ [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13], (active.state slot).dropWork.boxes = 0)
    (left right : BalancedWord) (table : MemoTable) (result : CommonEmbedding)
    (tableValue : active.state 105 = Slot.ofValue (encodeTable table))
    (leftValue : active.state 106 = .shared (encodeWord left)) (rightValue : active.state 107 = .shared (encodeWord right))
    (resultValue : active.state 108 = .shared (encodeResult result)) (resultView : active.state 109 = .shared (encodeResult result))
    {root104 : Binding} (bound104 : active.roots 104 = some root104)
    (empty104 : active.state 104 = .empty) (raw104 : world.memory[root104.address]? = some (.node .tuple 0 []))
    (heldAbove : ∀ slot ∈ [71, 85, 99], LocalOwnersAbove before.memory.length world active slot)
    (count : 110 ≤ active.count) :
    ∃ minimumFuel minimumBudget final after cost,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      after.state = (pairInsertMasks (active.forgetRefs (finishCode 32)).state).set 104
        (Slot.ofValue (encodeTable (.Entry ⟨left, right, result⟩ table))) ∧
      after.state 104 = Slot.ofValue (encodeTable (.Entry ⟨left, right, result⟩ table)) ∧
      (∀ slot ∈ [105, 106, 107, 108, 109], after.state slot = .empty) ∧
      (∀ slot ∈ [71, 85, 99], LocalOwnersAbove before.memory.length final after slot) ∧
      (∀ slot, slot ∉ [104, 105, 106, 107, 108, 109] →
        (active.forgetRefs (finishCode 32)).state slot = active.state slot → after.state slot = active.state slot) ∧
      (∀ slot binding, slot ≠ 104 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Derived.call (Recursive.original budget fuel) world (active.forgetRefs (finishCode 32)) callers .insert pairInsertArgs 104 = some (final, after, cost) ∧
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 33) [.call .insert pairInsertArgs 104] world active final after := by
  let observed := active.forgetRefs (finishCode 32)
  have machine := h.prepare (finishCode 32)
  have first : observed.state 105 = Slot.ofValue (encodeTable table) :=
    (LoanEnding.forget_closed (finishCode 32) _ (by rw [tableValue]; exact ofValue_typed (table_typed table)) (.adt .table)).trans tableValue
  have second : observed.state 106 = .shared (encodeWord left) :=
    (Activation.forgetRefs_observed active (finishCode 32) 106 (by decide +kernel)).trans leftValue
  have third : observed.state 107 = .shared (encodeWord right) :=
    (Activation.forgetRefs_observed active (finishCode 32) 107 (by decide +kernel)).trans rightValue
  have fourth : observed.state 108 = .shared (encodeResult result) :=
    (Activation.forgetRefs_observed active (finishCode 32) 108 (by decide +kernel)).trans resultValue
  have ended109 : observed.state 109 = .empty := LoanEnding.forget_ended_shared (finishCode 32) (List.range active.count)
    (by simp; omega) resultView (by decide +kernel)
  have arguments := pair_insert_arguments left right table result first second third fourth
  have typed : SnapshotFieldsTyped [encodeTable table, .reference (encodeWord left), .reference (encodeWord right), .reference (encodeResult result)]
      [.adt .table, .shared (.adt .word), .shared (.adt .word), .shared (.adt .embedding)] :=
    .cons (table_typed table) (.cons (.shared (word_typed left)) (.cons (.shared (word_typed right)) (.cons (.shared (result_typed result)) .nil)))
  have output : Types.callOutput .insert [.adt .table, .shared (.adt .word), .shared (.adt .word), .shared (.adt .embedding)] = some (.adt .table) := by
    simp only [Types.callOutput, reduceCtorEq, ite_false, Types.inputs, SourceTypes.sameList_refl, ite_true, Types.output]
  have emptyMasks : (pairInsertMasks observed.state) 104 = .empty := by
    simp only [pairInsertMasks, Partial.Locals.set, show (104 : Nat) ≠ 108 by decide, show (104 : Nat) ≠ 107 by decide,
      show (104 : Nat) ≠ 106 by decide, show (104 : Nat) ≠ 105 by decide, ite_false]
    exact LoanEnding.forget_empty (finishCode 32) (List.range active.count) empty104
  have preparedData := data.prepare (finishCode 32)
  have moves : ∀ current suspended, Scanned world observed current → Callers world callers suspended →
      ∀ op ∈ pairInsertArgs, Allowed world observed.roots (current.loans ++ suspended.reads) op := by
    intro current suspended scanned callerView op member
    simp only [pairInsertArgs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact allowed_table_local_with_origins machine preparedData scanned callerView first
    · obtain ⟨binding, hb⟩ := Activation.root_of_materialize machine.valid (value := .reference (encodeWord left)) (by rw [second]; simp only [Slot.materialize])
      exact machine.move_reference scanned callerView hb second
    · obtain ⟨binding, hb⟩ := Activation.root_of_materialize machine.valid (value := .reference (encodeWord right)) (by rw [third]; simp only [Slot.materialize])
      exact machine.move_reference scanned callerView hb third
    · obtain ⟨binding, hb⟩ := Activation.root_of_materialize machine.valid (value := .reference (encodeResult result)) (by rw [fourth]; simp only [Slot.materialize])
      exact machine.move_reference scanned callerView hb fourth
  have loans := Derived.RootLoansAllowed.of_safe_preserved (slot := 104) (active := {observed with state := pairInsertMasks observed.state})
    ((((machine.safe.clear 105).clear 106).clear 107).clear 108) raw104 (Or.inl rfl)
    h.previousCallers h.beforeWellFormed h.kept (h.fresh 104 root104 bound104)
  obtain ⟨minFuel, minBudget, final, after, cost, _, _, _, _, _, stable⟩ := Recursive.original_helper_call_stable
    machine.valid machine.callersValid machine.wellFormed machine.separate machine.ownerFrame machine.coverage
    .insert rfl pairInsertArgs bound104 arguments emptyMasks typed output (.adt .table) moves loans
  let sufficient := max minFuel (MemoSource.insertDepth left right result)
  have execute := (stable sufficient minBudget (Nat.le_max_left _ _) (by rfl)).1
  have source := (stable sufficient minBudget (Nat.le_max_left _ _) (by rfl)).2
  have ready := Derived.call_ready_from_values (callers := callers) machine.valid arguments typed output
  have respects := Recursive.original_typed_respects minBudget sufficient
  have callSpec := Derived.call_spec respects machine.valid machine.callersValid machine.wellFormed .insert pairInsertArgs 104 ready execute
  have safe := LoanSafeState.call_closed (Types.original_run_typed sufficient) arguments
    ((((machine.safe.clear 105).clear 106).clear 107).clear 108) typed output (.adt .table) source
  have native := machine.advance_call respects (Recursive.original_owns minBudget sufficient)
    .insert pairInsertArgs bound104 ready execute safe
  have roots := callSpec.2.2.2.1
  have countEq := callSpec.2.2.1
  obtain ⟨nativeCost, nativeRun, _⟩ := SourceEval.Helpers.insert_source table left right result sufficient (Nat.le_max_right _ _)
  have resultState : after.state = (pairInsertMasks observed.state).set 104 (Slot.ofValue (encodeTable (.Entry ⟨left, right, result⟩ table))) := by
    change SourceEval.action (SourceEval.run Certificate.original.body sufficient) observed.state (.call .insert pairInsertArgs 104) = some (after.state, cost) at source
    rw [SourceEval.action, arguments] at source
    simp only [bind, Option.bind] at source
    rw [nativeRun] at source
    exact (Prod.mk.inj (Option.some.inj source)).1.symm
  have value : after.state 104 = Slot.ofValue (encodeTable (.Entry ⟨left, right, result⟩ table)) := by
    rw [resultState]; simp only [Partial.Locals.set, ite_true]
  have emptyOthers : ∀ slot ∈ [105, 106, 107, 108, 109], after.state slot = .empty := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [resultState, pairInsertMasks, Partial.Locals.set, ended109]
  have original : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after := by
    refine ⟨native, ?_, ?_, ?_⟩
    · have wide : ClosedOutside [108, 109, 107, 106, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] after.state := by
        rw [resultState]
        exact (((((closed.forget (finishCode 32) _).clear 105).clear 106).clear 107).clear 108).set 104
          (ofValue_typed (table_typed (.Entry ⟨left, right, result⟩ table))) (.adt .table)
      intro slot outside
      by_cases temporary : slot ∈ [106, 107, 108, 109]
      · exact ⟨.u32, by rw [emptyOthers slot (by simpa using List.mem_cons_of_mem 105 temporary)]; exact .empty _, .u32⟩
      · exact wide slot (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside temporary ⊢; tauto)
    · intro slot member
      have different : slot ≠ 104 ∧ slot ≠ 105 ∧ slot ≠ 106 ∧ slot ≠ 107 ∧ slot ≠ 108 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
      rw [resultState]
      simp only [pairInsertMasks, Partial.Locals.set, different.1, different.2.1, different.2.2.1, different.2.2.2.1, different.2.2.2.2, ite_false]
      exact (Activation.forgetRefs_boxes active (finishCode 32) slot).trans (zero slot member)
    · intro slot member
      have different : slot ≠ 104 ∧ slot ≠ 105 ∧ slot ≠ 106 ∧ slot ≠ 107 ∧ slot ≠ 108 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
      obtain ⟨r, represented, bound⟩ := (origins slot member).prepare (finishCode 32)
      have sameMask : (pairInsertMasks observed.state) slot = observed.state slot := by
        simp [pairInsertMasks, Partial.Locals.set, different.2.1, different.2.2.1, different.2.2.2.1, different.2.2.2.2]
      have kept := Derived.call_preserves_other_local respects machine.valid machine.callersValid machine.wellFormed
        .insert pairInsertArgs 104 ready arguments sameMask different.1 (by
          change slot < active.count
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega) represented execute
      refine ⟨r, ?_, bound⟩
      rw [callSpec.2.1]
      apply (represented.transport kept).congr_at (congrFun roots slot)
      rw [resultState]
      simp [pairInsertMasks, observed, Partial.Locals.set, different.1, different.2.1, different.2.2.1, different.2.2.2.1, different.2.2.2.2]
  refine ⟨sufficient, minBudget, final, after, cost, original, roots, countEq, callSpec.2.1, resultState, value, emptyOthers, ?_, ?_, ?_, ?_⟩
  · intro slot member
    exact Derived.call_keeps_owner_provenance respects machine.valid machine.callersValid machine.wellFormed ready
      (by change slot < active.count; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl <;> decide +kernel) ((heldAbove slot member).prepare_any _) execute
  · intro slot outside same
    have different : slot ≠ 104 ∧ slot ≠ 105 ∧ slot ≠ 106 ∧ slot ≠ 107 ∧ slot ≠ 108 ∧ slot ≠ 109 := by simpa using outside
    rw [resultState]
    simpa only [pairInsertMasks, Partial.Locals.set, different.1, different.2.1, different.2.2.1, different.2.2.2.1, different.2.2.2.2.1, ite_false] using same
  · intro slot binding different root raw read
    have kept := Derived.call_preserves_other_root respects machine.valid machine.callersValid machine.wellFormed
      .insert pairInsertArgs 104 ready execute (other := slot) (target := binding) different root
    exact kept.reads binding.address (by simp) raw read
  · intro fuel budget fuelBound budgetBound
    have actual := (stable fuel budget ((Nat.le_max_left _ _).trans fuelBound) budgetBound).1
    exact ⟨actual, .cons (Calling.instruction_call_run actual) (.nil _ _)⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
