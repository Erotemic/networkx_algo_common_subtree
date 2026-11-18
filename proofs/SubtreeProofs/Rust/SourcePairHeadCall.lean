module

public import SubtreeProofs.Rust.SourcePairHeadArguments
public import SubtreeProofs.Rust.SourceEvaluatorCallTotality
public import SubtreeProofs.Rust.SourceOriginalLoanCalls

/-! Execute the actual pair/pair head recursive call from constructed native
arguments. The only recursive premise is universal totality for the smaller
head query pair; selected caller permissions and stable result storage follow
from the original-loan family without excluding query/table/caller aliases. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def headArgs : List Operand := [.move (.local 34), .move (.local 35), .move (.local 36)]
def headMasks (state : State) : State := ((state.set 34 .empty).set 35 .empty).set 36 .empty

theorem head_call_arguments {state : State} (left right : BalancedWord) (table : MemoTable)
    (first : state 34 = .shared (encodeWord left)) (second : state 35 = .shared (encodeWord right))
    (third : state 36 = Slot.ofValue (encodeTable table)) :
    SourceEval.operands state headArgs = some ([.reference (encodeWord left), .reference (encodeWord right), encodeTable table], headMasks state) := by
  have one := move_local_source (state := state) (slot := 34) (value := .reference (encodeWord left)) (by rw [first]; simp only [Slot.materialize])
  have two := move_local_source (state := state.set 34 .empty) (slot := 35) (value := .reference (encodeWord right)) (by
    simp only [Partial.Locals.set, show (35 : Nat) ≠ 34 by decide, ite_false, second, Slot.materialize])
  have three := move_local_source (state := (state.set 34 .empty).set 35 .empty) (value := encodeTable table) (slot := 36) (by
    simp only [Partial.Locals.set, show (36 : Nat) ≠ 35 by decide, show (36 : Nat) ≠ 34 by decide, ite_false, third, Slot.materialize_ofValue])
  simp only [headArgs, SourceEval.operands, one, two, three, bind, Option.bind]
  rfl

theorem pair_head_call_complete {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {lh lt rh rt : BalancedWord} {table : MemoTable} (scope : HeadArgumentScope initial lh lt rh rt table world active)
    (count : 37 ≤ active.count) (childTotal : NativeTotal lh rh) :
    ∃ minimumFuel minimumBudget final after result output cost,
      OriginalLoanMachine before callers previous external [35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      after.state 33 = Slot.ofValue (encodeOutput result output) ∧
      after.state 13 = queryTuple (.Pair lh lt) (.Pair rh rt) ∧
      (∀ slot ∈ [34, 35, 36], after.state slot = .empty) ∧
      memoized_common_embedding lh rh table = .ok (result, output) ∧
      after.state = (headMasks (active.forgetRefs (headCode 15)).state).set 33 (Slot.ofValue (encodeOutput result output)) ∧
      (∀ slot binding, slot ≠ 33 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Derived.call (Recursive.original budget fuel) world (active.forgetRefs (headCode 15)) callers .evaluate headArgs 33 = some (final, after, cost) ∧
        Calling.Prefix (Recursive.original budget fuel) callers (headCode 16) [.call .evaluate headArgs 33] world active final after := by
  let observed := active.forgetRefs (headCode 15)
  have machine := h.prepare (headCode 15)
  have left : observed.state 34 = .shared (encodeWord lh) :=
    (Activation.forgetRefs_observed active (headCode 15) 34 (by decide +kernel)).trans scope.left
  have right : observed.state 35 = .shared (encodeWord rh) :=
    (Activation.forgetRefs_observed active (headCode 15) 35 (by decide +kernel)).trans scope.right
  have tableValue : observed.state 36 = Slot.ofValue (encodeTable table) :=
    (h.prepare_closed_local (headCode 15) 36 (by decide)).trans scope.table
  have tuple : observed.state 13 = queryTuple (.Pair lh lt) (.Pair rh rt) := prepare_queryTuple scope.tuple _
  obtain ⟨root33, bound33, raw33⟩ := scope.result
  have arguments := head_call_arguments lh rh table left right tableValue
  have empty : headMasks observed.state 33 = .empty := by
    simp only [headMasks, Partial.Locals.set, show (33 : Nat) ≠ 36 by decide, show (33 : Nat) ≠ 35 by decide,
      show (33 : Nat) ≠ 34 by decide, ite_false]
    exact LoanEnding.forget_empty _ _ scope.resultEmpty
  have safe := ((machine.native.safe.clear 34).clear 35).clear 36
  have typed : SnapshotFieldsTyped [.reference (encodeWord lh), .reference (encodeWord rh), encodeTable table]
      [.shared (.adt .word), .shared (.adt .word), .adt .table] :=
    .cons (.shared (word_typed lh)) (.cons (.shared (word_typed rh)) (.cons (table_typed table) .nil))
  have outputType : Types.callOutput .evaluate [.shared (.adt .word), .shared (.adt .word), .adt .table] =
      some (.tuple [.adt .optional, .adt .table]) := by
    simp only [Types.callOutput, reduceCtorEq, ite_false, Types.inputs, SourceTypes.sameList_refl, ite_true, Types.output]
  have moves : ∀ current suspended, Scanned world observed current → Callers world callers suspended →
      ∀ op ∈ headArgs, Allowed world observed.roots (current.loans ++ suspended.reads) op := by
    intro current suspended scanned callerView op member
    simp only [headArgs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact machine.moves scanned callerView trivial
  have loans := Derived.RootLoansAllowed.of_safe_preserved (slot := 33) (active := {observed with state := headMasks observed.state})
    safe raw33 (Or.inl rfl) h.native.previousCallers h.native.beforeWellFormed h.native.kept (h.native.fresh 33 root33 bound33)
  obtain ⟨fuel, budget, final, after, result, output, cost, state, native, _, _, _, _, _, stable⟩ :=
    Derived.evaluator_call_total machine.native.valid machine.native.callersValid machine.native.wellFormed machine.native.separate
      machine.native.ownerFrame machine.native.coverage lh rh table childTotal headArgs bound33 arguments empty moves loans
  have execute := (stable fuel budget (by rfl) (by rfl)).1
  have ready := Derived.call_ready_from_values (callers := callers) machine.native.valid arguments typed outputType
  have callSpec := Derived.call_spec (Recursive.original_typed_respects budget fuel) machine.native.valid machine.native.callersValid machine.native.wellFormed
    .evaluate headArgs 33 ready execute
  have original := machine.advance_call (Recursive.original_typed_respects budget fuel) (Recursive.original_owns budget fuel)
    .evaluate headArgs bound33 (by decide) ready arguments safe (((machine.closed.clear 34).clear 35).clear 36)
    (by intro index member
        by_cases first : index = 34
        · subst index; right; simp [headMasks, Partial.Locals.set]
        by_cases second : index = 35
        · subst index; right; simp [headMasks, Partial.Locals.set]
        by_cases third : index = 36
        · subst index; right; simp [headMasks, Partial.Locals.set]
        · left; simp only [headMasks, Partial.Locals.set, first, second, third, ite_false, observed])
    (by intro index member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> change _ < active.count <;> omega)
    (encodeOutput_typed result output) (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) state execute
  refine ⟨fuel, budget, final, after, result, output, cost, original, callSpec.2.2.2.1, callSpec.2.2.1, callSpec.2.1, ?_, ?_, ?_, native, state, ?_, ?_⟩
  · rw [state]; simp only [Partial.Locals.set, ite_true]
  · rw [state]; simpa [headMasks, Partial.Locals.set] using tuple
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp [state, headMasks, Partial.Locals.set]
  · intro slot binding different root raw read
    have kept := Derived.call_preserves_other_root (Recursive.original_typed_respects budget fuel)
      machine.native.valid machine.native.callersValid machine.native.wellFormed .evaluate headArgs 33 ready execute different root
    exact kept.reads binding.address (by simp) raw read
  · intro largerFuel largerBudget fuelBound budgetBound
    have actual := (stable largerFuel largerBudget fuelBound budgetBound).1
    exact ⟨actual, .cons (Calling.instruction_call_run actual) (.nil _ _)⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
