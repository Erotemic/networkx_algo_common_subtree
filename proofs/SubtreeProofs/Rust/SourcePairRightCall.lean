module

public import SubtreeProofs.Rust.SourcePairRightCallArguments
public import SubtreeProofs.Rust.SourceAnchoredLoanCalls
public import SubtreeProofs.Rust.SourceEvaluatorCallTotality

/-! Execute the actual right contraction call from constructed arguments.
The recursive premise is totality for the strictly smaller concatenated native
request. Original query loans and fresh word-supported loans remain separate. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def rightContractionArgs : List Operand := [.move (.local 91), .move (.local 92), .move (.local 94)]
def rightContractionMasks (state : State) : State := ((state.set 91 .empty).set 92 .empty).set 94 .empty

theorem right_contraction_call_arguments {state : State} (left right : BalancedWord) (table : MemoTable)
    (first : state 91 = .shared (encodeWord left)) (second : state 92 = .shared (encodeWord right))
    (third : state 94 = Slot.ofValue (encodeTable table)) :
    SourceEval.operands state rightContractionArgs =
      some ([.reference (encodeWord left), .reference (encodeWord right), encodeTable table], rightContractionMasks state) := by
  have one := move_local_source (state := state) (slot := 91) (value := .reference (encodeWord left))
    (by rw [first]; simp only [Slot.materialize])
  have two := move_local_source (state := state.set 91 .empty) (slot := 92) (value := .reference (encodeWord right))
    (by simp only [Partial.Locals.set, show (92 : Nat) ≠ 91 by decide, ite_false, second, Slot.materialize])
  have three := move_local_source (state := (state.set 91 .empty).set 92 .empty) (slot := 94) (value := encodeTable table)
    (by simp only [Partial.Locals.set, show (94 : Nat) ≠ 92 by decide, show (94 : Nat) ≠ 91 by decide, ite_false,
          third, Slot.materialize_ofValue])
  simp only [rightContractionArgs, SourceEval.operands, one, two, three, bind, Option.bind]
  rfl

theorem pair_right_call_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat} {anchor : Resources}
    {lh lt rh rt : BalancedWord} {heads tails leftWitness : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (h : AnchoredLoanMachine before callers previous external [91, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13]
      [92, 93] 85 (OrderedSolver.appendWord rh rt) anchor world active)
    (scope : RightContractionArgumentScope (.Pair lh lt) (OrderedSolver.appendWord rh rt) table world active)
    (held : RightHeldScope lh lt rh rt heads tails leftWitness total active)
    (count : 95 ≤ active.count) (childTotal : NativeTotal (.Pair lh lt) (OrderedSolver.appendWord rh rt)) :
    ∃ minimumFuel minimumBudget final after result output cost,
      AnchoredLoanMachine before callers previous external [91, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13]
        [92, 93] 85 (OrderedSolver.appendWord rh rt) anchor final after ∧
      RightHeldScope lh lt rh rt heads tails leftWitness total after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      after.state 90 = Slot.ofValue (encodeOutput result output) ∧ after.state 75 = .empty ∧
      (∀ slot ∈ [91, 92, 94], after.state slot = .empty) ∧
      memoized_common_embedding (.Pair lh lt) (OrderedSolver.appendWord rh rt) table = .ok (result, output) ∧
      after.state = (rightContractionMasks (active.forgetRefs (rightCode 24)).state).set 90 (Slot.ofValue (encodeOutput result output)) ∧
      (∀ slot binding, slot ≠ 90 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Derived.call (Recursive.original budget fuel) world (active.forgetRefs (rightCode 24)) callers
          .evaluate rightContractionArgs 90 = some (final, after, cost) ∧
        Calling.Prefix (Recursive.original budget fuel) callers (rightCode 25)
          [.call .evaluate rightContractionArgs 90] world active final after := by
  let observed := active.forgetRefs (rightCode 24)
  have machine := h.prepare (rightCode 24)
  have left : observed.state 91 = .shared (encodeWord (.Pair lh lt)) :=
    (Activation.forgetRefs_observed active (rightCode 24) 91 (by decide +kernel)).trans scope.left
  have right : observed.state 92 = .shared (encodeWord (OrderedSolver.appendWord rh rt)) :=
    (Activation.forgetRefs_observed active (rightCode 24) 92 (by decide +kernel)).trans scope.right
  have tableValue : observed.state 94 = Slot.ofValue (encodeTable table) :=
    (LoanEnding.forget_closed _ _ (by rw [scope.tableValue]; exact ofValue_typed (table_typed table)) (.adt .table)).trans scope.tableValue
  obtain ⟨root76, bound76, raw76⟩ := scope.result
  have arguments := right_contraction_call_arguments (.Pair lh lt) (OrderedSolver.appendWord rh rt) table left right tableValue
  have empty : rightContractionMasks observed.state 90 = .empty := by
    simp only [rightContractionMasks, Partial.Locals.set, show (90 : Nat) ≠ 94 by decide,
      show (90 : Nat) ≠ 92 by decide, show (90 : Nat) ≠ 91 by decide, ite_false]
    exact LoanEnding.forget_empty (rightCode 24) _ scope.resultEmpty
  have safe := ((machine.native.safe.clear 91).clear 92).clear 94
  have typed : SnapshotFieldsTyped [.reference (encodeWord (.Pair lh lt)), .reference (encodeWord (OrderedSolver.appendWord rh rt)), encodeTable table]
      [.shared (.adt .word), .shared (.adt .word), .adt .table] :=
    .cons (.shared (word_typed _)) (.cons (.shared (word_typed _)) (.cons (table_typed table) .nil))
  have outputType : Types.callOutput .evaluate [.shared (.adt .word), .shared (.adt .word), .adt .table] =
      some (.tuple [.adt .optional, .adt .table]) := by
    simp only [Types.callOutput, reduceCtorEq, ite_false, Types.inputs, SourceTypes.sameList_refl, ite_true, Types.output]
  have moves : ∀ current suspended, Scanned world observed current → Callers world callers suspended →
      ∀ op ∈ rightContractionArgs, Allowed world observed.roots (current.loans ++ suspended.reads) op := by
    intro current suspended scanned callerView op member
    simp only [rightContractionArgs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · obtain ⟨binding, root⟩ := scope.bound 91 (by simp)
      exact machine.move_local root (by decide) scanned callerView
    · obtain ⟨binding, root⟩ := scope.bound 92 (by simp)
      exact machine.move_local root (by decide) scanned callerView
    · obtain ⟨binding, root⟩ := scope.bound 94 (by simp)
      exact machine.move_local root (by decide) scanned callerView
  have loans := Derived.RootLoansAllowed.of_safe_preserved (slot := 90)
    (active := {observed with state := rightContractionMasks observed.state}) safe raw76 (Or.inl rfl)
    h.native.previousCallers h.native.beforeWellFormed h.native.kept (h.native.fresh 90 root76 bound76)
  obtain ⟨fuel, budget, final, after, result, output, cost, state, native, _, _, _, _, _, stable⟩ :=
    Derived.evaluator_call_total machine.native.valid machine.native.callersValid machine.native.wellFormed machine.native.separate
      machine.native.ownerFrame machine.native.coverage (.Pair lh lt) (OrderedSolver.appendWord rh rt) table childTotal
      rightContractionArgs bound76 arguments empty moves loans
  have execute := (stable fuel budget (by rfl) (by rfl)).1
  have ready := Derived.call_ready_from_values (callers := callers) machine.native.valid arguments typed outputType
  have checked := Derived.call_spec (Recursive.original_typed_respects budget fuel) machine.native.valid machine.native.callersValid
    machine.native.wellFormed .evaluate rightContractionArgs 90 ready execute
  have anchored := machine.advance_call (Recursive.original_typed_respects budget fuel) (Recursive.original_owns budget fuel)
    .evaluate rightContractionArgs bound76 (by decide) (by decide) ready arguments safe
    (((machine.closed.clear 91).clear 92).clear 94)
    (by intro index member
        by_cases one : index = 91
        · subst index; right; simp [rightContractionMasks, Partial.Locals.set]
        by_cases two : index = 92
        · subst index; right; simp [rightContractionMasks, Partial.Locals.set]
        by_cases three : index = 94
        · subst index; right; simp [rightContractionMasks, Partial.Locals.set]
        · left; simp only [rightContractionMasks, Partial.Locals.set, one, two, three, ite_false, observed])
    (by intro index member
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with (rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> change _ < active.count <;> omega)
    (by simp only [observed, rightContractionMasks, Partial.Locals.set, show (85 : Nat) ≠ 94 by decide,
          show (85 : Nat) ≠ 92 by decide, show (85 : Nat) ≠ 91 by decide, ite_false])
    (encodeOutput_typed result output) (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) state execute
  have actualPrefix : Calling.Prefix (Recursive.original budget fuel) callers (rightCode 25) [.call .evaluate rightContractionArgs 90] world active final after :=
    .cons (Calling.instruction_call_run execute) (.nil _ _)
  have heldAfter := held.through_prefix actualPrefix
    (by intro slot member
        simp only [pairSharedQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
    (by intro slot member
        simp only [pairQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
    (by intro slot member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
    (by intro slot member act actMember
        cases List.mem_singleton.mp actMember
        trivial)
  refine ⟨fuel, budget, final, after, result, output, cost, anchored, heldAfter,
    checked.2.2.2.1, checked.2.2.1, checked.2.1, ?_, ?_, ?_, native, state, ?_, ?_⟩
  · rw [state]; simp only [Partial.Locals.set, ite_true]
  · exact (actualPrefix.closed_local_same_calls (index := 75) (by rw [scope.tableMoved]; exact .empty .u32) .u32 (by decide +kernel)).trans scope.tableMoved
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp [state, rightContractionMasks, Partial.Locals.set]
  · intro slot binding different root raw memoryRead
    have kept := Derived.call_preserves_other_root (Recursive.original_typed_respects budget fuel)
      machine.native.valid machine.native.callersValid machine.native.wellFormed .evaluate rightContractionArgs 90 ready execute different root
    exact kept.reads binding.address (by simp) raw memoryRead
  · intro largerFuel largerBudget fuelBound budgetBound
    have actual := (stable largerFuel largerBudget fuelBound budgetBound).1
    exact ⟨actual, .cons (Calling.instruction_call_run actual) (.nil _ _)⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
