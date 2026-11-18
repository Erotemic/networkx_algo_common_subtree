module

public import SubtreeProofs.Rust.SourcePairLeftCallArguments
public import SubtreeProofs.Rust.SourceAnchoredLoanCalls
public import SubtreeProofs.Rust.SourceEvaluatorCallTotality

/-! Execute the actual left contraction call from constructed arguments.
The recursive premise is totality for the strictly smaller concatenated native
request. Original query loans and fresh word-supported loans remain separate. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def leftContractionArgs : List Operand := [.move (.local 77), .move (.local 79), .move (.local 80)]
def leftContractionMasks (state : State) : State := ((state.set 77 .empty).set 79 .empty).set 80 .empty

theorem left_contraction_call_arguments {state : State} (left right : BalancedWord) (table : MemoTable)
    (first : state 77 = .shared (encodeWord left)) (second : state 79 = .shared (encodeWord right))
    (third : state 80 = Slot.ofValue (encodeTable table)) :
    SourceEval.operands state leftContractionArgs =
      some ([.reference (encodeWord left), .reference (encodeWord right), encodeTable table], leftContractionMasks state) := by
  have one := move_local_source (state := state) (slot := 77) (value := .reference (encodeWord left))
    (by rw [first]; simp only [Slot.materialize])
  have two := move_local_source (state := state.set 77 .empty) (slot := 79) (value := .reference (encodeWord right))
    (by simp only [Partial.Locals.set, show (79 : Nat) ≠ 77 by decide, ite_false, second, Slot.materialize])
  have three := move_local_source (state := (state.set 77 .empty).set 79 .empty) (slot := 80) (value := encodeTable table)
    (by simp only [Partial.Locals.set, show (80 : Nat) ≠ 79 by decide, show (80 : Nat) ≠ 77 by decide, ite_false,
          third, Slot.materialize_ofValue])
  simp only [leftContractionArgs, SourceEval.operands, one, two, three, bind, Option.bind]
  rfl

theorem pair_left_call_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat} {anchor : Resources}
    {lh lt rh rt : BalancedWord} {heads tails : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (h : AnchoredLoanMachine before callers previous external [79, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13]
      [77, 78] 71 (OrderedSolver.appendWord lh lt) anchor world active)
    (scope : LeftContractionArgumentScope (OrderedSolver.appendWord lh lt) (.Pair rh rt) table world active)
    (queries : PairQueryScope lh lt rh rt active) (candidate : MatchedCandidateScope heads tails total active)
    (count : 81 ≤ active.count) (childTotal : NativeTotal (OrderedSolver.appendWord lh lt) (.Pair rh rt)) :
    ∃ minimumFuel minimumBudget final after result output cost,
      AnchoredLoanMachine before callers previous external [79, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13]
        [77, 78] 71 (OrderedSolver.appendWord lh lt) anchor final after ∧
      PairQueryScope lh lt rh rt after ∧ MatchedCandidateScope heads tails total after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      after.state 76 = Slot.ofValue (encodeOutput result output) ∧ after.state 42 = .empty ∧
      (∀ slot ∈ [77, 79, 80], after.state slot = .empty) ∧
      memoized_common_embedding (OrderedSolver.appendWord lh lt) (.Pair rh rt) table = .ok (result, output) ∧
      after.state = (leftContractionMasks (active.forgetRefs (matchedCode 48)).state).set 76 (Slot.ofValue (encodeOutput result output)) ∧
      (∀ slot binding, slot ≠ 76 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Derived.call (Recursive.original budget fuel) world (active.forgetRefs (matchedCode 48)) callers
          .evaluate leftContractionArgs 76 = some (final, after, cost) ∧
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 49)
          [.call .evaluate leftContractionArgs 76] world active final after := by
  let observed := active.forgetRefs (matchedCode 48)
  have machine := h.prepare (matchedCode 48)
  have left : observed.state 77 = .shared (encodeWord (OrderedSolver.appendWord lh lt)) :=
    (Activation.forgetRefs_observed active (matchedCode 48) 77 (by decide +kernel)).trans scope.left
  have right : observed.state 79 = .shared (encodeWord (.Pair rh rt)) :=
    (Activation.forgetRefs_observed active (matchedCode 48) 79 (by decide +kernel)).trans scope.right
  have tableValue : observed.state 80 = Slot.ofValue (encodeTable table) :=
    (LoanEnding.forget_closed _ _ (by rw [scope.tableValue]; exact ofValue_typed (table_typed table)) (.adt .table)).trans scope.tableValue
  obtain ⟨root76, bound76, raw76⟩ := scope.result
  have arguments := left_contraction_call_arguments (OrderedSolver.appendWord lh lt) (.Pair rh rt) table left right tableValue
  have empty : leftContractionMasks observed.state 76 = .empty := by
    simp only [leftContractionMasks, Partial.Locals.set, show (76 : Nat) ≠ 80 by decide,
      show (76 : Nat) ≠ 79 by decide, show (76 : Nat) ≠ 77 by decide, ite_false]
    exact LoanEnding.forget_empty (matchedCode 48) _ scope.resultEmpty
  have safe := ((machine.native.safe.clear 77).clear 79).clear 80
  have typed : SnapshotFieldsTyped [.reference (encodeWord (OrderedSolver.appendWord lh lt)), .reference (encodeWord (.Pair rh rt)), encodeTable table]
      [.shared (.adt .word), .shared (.adt .word), .adt .table] :=
    .cons (.shared (word_typed _)) (.cons (.shared (word_typed _)) (.cons (table_typed table) .nil))
  have outputType : Types.callOutput .evaluate [.shared (.adt .word), .shared (.adt .word), .adt .table] =
      some (.tuple [.adt .optional, .adt .table]) := by
    simp only [Types.callOutput, reduceCtorEq, ite_false, Types.inputs, SourceTypes.sameList_refl, ite_true, Types.output]
  have moves : ∀ current suspended, Scanned world observed current → Callers world callers suspended →
      ∀ op ∈ leftContractionArgs, Allowed world observed.roots (current.loans ++ suspended.reads) op := by
    intro current suspended scanned callerView op member
    simp only [leftContractionArgs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · obtain ⟨binding, root⟩ := scope.bound 77 (by simp)
      exact machine.move_local root (by decide) scanned callerView
    · obtain ⟨binding, root⟩ := scope.bound 79 (by simp)
      exact machine.move_local root (by decide) scanned callerView
    · obtain ⟨binding, root⟩ := scope.bound 80 (by simp)
      exact machine.move_local root (by decide) scanned callerView
  have loans := Derived.RootLoansAllowed.of_safe_preserved (slot := 76)
    (active := {observed with state := leftContractionMasks observed.state}) safe raw76 (Or.inl rfl)
    h.native.previousCallers h.native.beforeWellFormed h.native.kept (h.native.fresh 76 root76 bound76)
  obtain ⟨fuel, budget, final, after, result, output, cost, state, native, _, _, _, _, _, stable⟩ :=
    Derived.evaluator_call_total machine.native.valid machine.native.callersValid machine.native.wellFormed machine.native.separate
      machine.native.ownerFrame machine.native.coverage (OrderedSolver.appendWord lh lt) (.Pair rh rt) table childTotal
      leftContractionArgs bound76 arguments empty moves loans
  have execute := (stable fuel budget (by rfl) (by rfl)).1
  have ready := Derived.call_ready_from_values (callers := callers) machine.native.valid arguments typed outputType
  have checked := Derived.call_spec (Recursive.original_typed_respects budget fuel) machine.native.valid machine.native.callersValid
    machine.native.wellFormed .evaluate leftContractionArgs 76 ready execute
  have anchored := machine.advance_call (Recursive.original_typed_respects budget fuel) (Recursive.original_owns budget fuel)
    .evaluate leftContractionArgs bound76 (by decide) (by decide) ready arguments safe
    (((machine.closed.clear 77).clear 79).clear 80)
    (by intro index member
        by_cases one : index = 77
        · subst index; right; simp [leftContractionMasks, Partial.Locals.set]
        by_cases two : index = 79
        · subst index; right; simp [leftContractionMasks, Partial.Locals.set]
        by_cases three : index = 80
        · subst index; right; simp [leftContractionMasks, Partial.Locals.set]
        · left; simp only [leftContractionMasks, Partial.Locals.set, one, two, three, ite_false, observed])
    (by intro index member
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with (rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> change _ < active.count <;> omega)
    (by simp only [observed, leftContractionMasks, Partial.Locals.set, show (71 : Nat) ≠ 80 by decide,
          show (71 : Nat) ≠ 79 by decide, show (71 : Nat) ≠ 77 by decide, ite_false])
    (encodeOutput_typed result output) (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) state execute
  have actualPrefix : Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 49) [.call .evaluate leftContractionArgs 76] world active final after :=
    .cons (Calling.instruction_call_run execute) (.nil _ _)
  have queriesAfter : PairQueryScope lh lt rh rt after := by
    apply prefix_pair_queries_complete actualPrefix queries
    · intro slot member
      simp only [pairSharedQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    · intro slot member
      simp only [pairQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have candidateAfter := candidate.through_prefix actualPrefix
    (by intro slot member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide +kernel)
    (by intro slot member act actMember
        cases List.mem_singleton.mp actMember
        trivial)
  refine ⟨fuel, budget, final, after, result, output, cost, anchored, queriesAfter, candidateAfter,
    checked.2.2.2.1, checked.2.2.1, checked.2.1, ?_, ?_, ?_, native, state, ?_, ?_⟩
  · rw [state]; simp only [Partial.Locals.set, ite_true]
  · exact (actualPrefix.closed_local_same_calls (index := 42) (by rw [scope.tableMoved]; exact .empty .u32) .u32 (by decide +kernel)).trans scope.tableMoved
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp [state, leftContractionMasks, Partial.Locals.set]
  · intro slot binding different root raw memoryRead
    have kept := Derived.call_preserves_other_root (Recursive.original_typed_respects budget fuel)
      machine.native.valid machine.native.callersValid machine.native.wellFormed .evaluate leftContractionArgs 76 ready execute different root
    exact kept.reads binding.address (by simp) raw memoryRead
  · intro largerFuel largerBudget fuelBound budgetBound
    have actual := (stable largerFuel largerBudget fuelBound budgetBound).1
    exact ⟨actual, .cons (Calling.instruction_call_run actual) (.nil _ _)⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
