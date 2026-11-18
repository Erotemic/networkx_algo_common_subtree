module

public import SubtreeProofs.Rust.SourceEvaluatorBorrowPrefix
public import SubtreeProofs.Rust.SourceRecursiveHelperCallTotality
public import SubtreeProofs.Rust.SourceLoanSafeCalls
public import SubtreeProofs.Rust.SourceOwnerRecursive

/-! Construct the evaluator's common lookup call from its native table/query
locals. Native graph shape and old-caller preservation discharge every selected
reference move and destination loan guard; no successful callee is a premise. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def lookupArgs : List Operand := [.move (.local 5), .move (.local 7), .move (.local 8)]

def afterLookup : Code :=
  .step (.storageDead 8) <| .step (.storageDead 7) <| .step (.storageDead 5) <|
  .switch (.discriminant (.local 4)) [(.variant .optional 1, 0)] (some 1) cacheHit cacheMiss returnResult

theorem lookupSuffix_step : lookupSuffix = .step (.call .lookup lookupArgs 4) afterLookup := rfl

theorem body_lookup_prefix : body =
    (borrowPrefix ++ [Action.call .lookup lookupArgs 4]).foldr Control.Tree.step afterLookup := by
  rw [body_borrow_prefix, List.foldr_append]
  rfl

theorem actual_body_lookup_prefix : Certificate.original.body .evaluate =
    (borrowPrefix ++ [Action.call .lookup lookupArgs 4]).foldr Control.Tree.step afterLookup :=
  actual_body.trans body_lookup_prefix

theorem lookup_arguments {state : State} (left right : BalancedWord) (table : MemoTable)
    (first : state 5 = .shared (encodeTable table)) (second : state 7 = .shared (encodeWord left))
    (third : state 8 = .shared (encodeWord right)) :
    SourceEval.operands state lookupArgs = some
      ([.reference (encodeTable table), .reference (encodeWord left), .reference (encodeWord right)],
       ((state.set 5 .empty).set 7 .empty).set 8 .empty) := by
  simp [lookupArgs, SourceEval.operands, SourceEval.operand, Partial.Locals.move, splitPlace,
    Slot.take, Slot.materialize, first, second, third, Partial.Locals.set]

theorem lookup_call_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active)
    (left right : BalancedWord) (table : MemoTable) {resultRoot tableView leftView rightView : Binding}
    (resultBinding : active.roots 4 = some resultRoot) (tableBinding : active.roots 5 = some tableView)
    (leftBinding : active.roots 7 = some leftView) (rightBinding : active.roots 8 = some rightView)
    (destination : world.memory[resultRoot.address]? = some (.node .tuple 0 []))
    (empty : active.state 4 = .empty) (tableValue : active.state 5 = .shared (encodeTable table))
    (leftValue : active.state 7 = .shared (encodeWord left)) (rightValue : active.state 8 = .shared (encodeWord right)) :
    ∃ minimumFuel minimumBudget final after cost,
      after.Valid final ∧ final.WellFormed ∧ (∀ caller ∈ callers, caller.Valid final) ∧
      OwnerFrame final (after.owners final ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (after.owners final ++ (callerOwners final callers ++ external)) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Derived.call (Recursive.original budget fuel) world (active.forgetRefs lookupSuffix) callers .lookup lookupArgs 4 =
          some (final, after, cost) ∧
        SourceEval.action (SourceEval.run Certificate.original.body fuel) (active.forgetRefs lookupSuffix).state
          (.call .lookup lookupArgs 4) = some (after.state, cost) := by
  let observed := active.forgetRefs lookupSuffix
  have machine := h.prepare lookupSuffix
  have first : observed.state 5 = .shared (encodeTable table) := by
    rw [Activation.forgetRefs_observed active lookupSuffix 5 (by decide +kernel)]; exact tableValue
  have second : observed.state 7 = .shared (encodeWord left) := by
    rw [Activation.forgetRefs_observed active lookupSuffix 7 (by decide +kernel)]; exact leftValue
  have third : observed.state 8 = .shared (encodeWord right) := by
    rw [Activation.forgetRefs_observed active lookupSuffix 8 (by decide +kernel)]; exact rightValue
  have source := lookup_arguments left right table first second third
  have emptyMasks : (((observed.state.set 5 .empty).set 7 .empty).set 8 .empty) 4 = .empty := by
    have original : observed.state 4 = .empty := LoanEnding.forget_empty lookupSuffix _ empty
    simpa [Partial.Locals.set] using original
  have moves : ∀ current suspended, Scanned world observed current → Callers world callers suspended →
      ∀ op ∈ lookupArgs, Allowed world observed.roots (current.loans ++ suspended.reads) op := by
    intro current suspended scanned callerView op member
    simp only [lookupArgs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact machine.move_reference scanned callerView tableBinding first
    · exact machine.move_reference scanned callerView leftBinding second
    · exact machine.move_reference scanned callerView rightBinding third
  have loans := Derived.RootLoansAllowed.of_safe_preserved (slot := 4)
    (active := {observed with state := ((observed.state.set 5 .empty).set 7 .empty).set 8 .empty})
    (((machine.safe.clear 5).clear 7).clear 8) destination (Or.inl rfl)
    h.previousCallers h.beforeWellFormed h.kept (h.fresh 4 resultRoot resultBinding)
  exact Recursive.original_helper_call_stable machine.valid machine.callersValid machine.wellFormed machine.separate
    machine.ownerFrame machine.coverage .lookup rfl lookupArgs resultBinding source emptyMasks
    (.cons (.shared (table_typed table)) (.cons (.shared (word_typed left)) (.cons (.shared (word_typed right)) .nil)))
    (by simp only [Types.callOutput, reduceCtorEq, ite_false, Types.inputs, SourceTypes.sameList_refl, ite_true, Types.output])
    (.adt .optional) moves loans

theorem lookup_call_machine (budget fuel : Nat) {before world final : World} {active after : Activation}
    {callers : List Activation} {previous : Resources} {external : List Nat} {cost : Cost}
    (h : LoanSafeMachine before callers previous external world active)
    (left right : BalancedWord) (table : MemoTable) {resultRoot : Binding}
    (resultBinding : active.roots 4 = some resultRoot)
    (tableValue : active.state 5 = .shared (encodeTable table))
    (leftValue : active.state 7 = .shared (encodeWord left)) (rightValue : active.state 8 = .shared (encodeWord right))
    (run : Derived.call (Recursive.original budget fuel) world (active.forgetRefs lookupSuffix) callers .lookup lookupArgs 4 =
      some (final, after, cost)) : LoanSafeMachine before callers previous external final after := by
  let observed := active.forgetRefs lookupSuffix
  have machine := h.prepare lookupSuffix
  have first : observed.state 5 = .shared (encodeTable table) := by
    rw [Activation.forgetRefs_observed active lookupSuffix 5 (by decide +kernel)]; exact tableValue
  have second : observed.state 7 = .shared (encodeWord left) := by
    rw [Activation.forgetRefs_observed active lookupSuffix 7 (by decide +kernel)]; exact leftValue
  have third : observed.state 8 = .shared (encodeWord right) := by
    rw [Activation.forgetRefs_observed active lookupSuffix 8 (by decide +kernel)]; exact rightValue
  have source := lookup_arguments left right table first second third
  have typed : SnapshotFieldsTyped [.reference (encodeTable table), .reference (encodeWord left), .reference (encodeWord right)]
      [.shared (.adt .table), .shared (.adt .word), .shared (.adt .word)] :=
    .cons (.shared (table_typed table)) (.cons (.shared (word_typed left)) (.cons (.shared (word_typed right)) .nil))
  have output : Types.callOutput .lookup [.shared (.adt .table), .shared (.adt .word), .shared (.adt .word)] = some (.adt .optional) := by
    simp only [Types.callOutput, reduceCtorEq, ite_false, Types.inputs, SourceTypes.sameList_refl, ite_true, Types.output]
  have ready := Derived.call_ready_from_values (callers := callers) machine.valid source typed output
  have reflected := (Derived.call_spec (Recursive.original_typed_respects budget fuel) machine.valid machine.callersValid
    machine.wellFormed .lookup lookupArgs 4 ready run).1
  have safe := LoanSafeState.call_closed (Types.original_run_typed fuel) source
    (((machine.safe.clear 5).clear 7).clear 8) typed output (.adt .optional) reflected
  exact machine.advance_call (Recursive.original_typed_respects budget fuel) (Recursive.original_owns budget fuel)
    .lookup lookupArgs resultBinding ready run safe

theorem lookup_prefix_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active)
    (count : 9 ≤ active.count) (left right : BalancedWord) (table : MemoTable)
    (inputs : InputLocals left right table active.state)
    (unbound : ∀ slot ∈ [0, 4, 5, 6, 7, 8], active.roots slot = none) :
    ∃ minimumFuel minimumBudget final after,
      after.Valid final ∧ final.WellFormed ∧ (∀ caller ∈ callers, caller.Valid final) ∧
      OwnerFrame final (after.owners final ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (after.owners final ++ (callerOwners final callers ++ external)) ∧
      LoanSafeMachine before callers previous external final after ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers afterLookup
          (borrowPrefix ++ [Action.call .lookup lookupArgs 4]) world active final after := by
  obtain ⟨middle, current, resultRoot, tableView, leftView, rightView, steps, machine, _, _,
    resultBinding, tableBinding, leftBinding, rightBinding, destination, empty, tableValue, leftValue, rightValue, _, _, _, _, _⟩ :=
    borrow_prefix_complete h (Helpers.callee 0 0) count left right table inputs unbound
  obtain ⟨minFuel, minBudget, final, after, cost, valid, wf, callersValid, frame, coverage, stable⟩ :=
    lookup_call_complete machine left right table resultBinding tableBinding leftBinding rightBinding
      destination empty tableValue leftValue rightValue
  have finalMachine := lookup_call_machine minBudget minFuel machine left right table resultBinding tableValue leftValue rightValue
    (stable minFuel minBudget (by omega) (by omega)).1
  refine ⟨minFuel, minBudget, final, after, valid, wf, callersValid, frame, coverage, finalMachine, ?_⟩
  intro fuel budget fuelBound budgetBound
  have beforeCall := steps.noncall_callee (Recursive.original budget fuel) (by decide +kernel)
  have call := (stable fuel budget fuelBound budgetBound).1
  exact beforeCall.append (.cons (Calling.instruction_call_run call) (.nil final after))

end SubtreeProofs.Rust.SourceEval.Evaluator
