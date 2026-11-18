module

public import SubtreeProofs.Rust.SourceEvaluatorCallTotality
public import SubtreeProofs.Rust.SourceOriginalLoanCalls

/-! Construct an evaluator call at arbitrary actual local slots when every
current shared loan is original. This reuses the smaller native contract and
retains canonical origins, exact output masks and stable whole-call costs. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def nativeCallArgs (left right table : Nat) : List Operand := [.move (.local left), .move (.local right), .move (.local table)]
def nativeCallMasks (left right table : Nat) (state : State) : State := ((state.set left .empty).set right .empty).set table .empty

theorem native_call_arguments {state : State} (l r t : Nat) (lr : l ≠ r) (lt : l ≠ t) (rt : r ≠ t)
    (left right : BalancedWord) (table : MemoTable) (first : state l = .shared (encodeWord left))
    (second : state r = .shared (encodeWord right)) (third : state t = Slot.ofValue (encodeTable table)) :
    SourceEval.operands state (nativeCallArgs l r t) =
      some ([.reference (encodeWord left), .reference (encodeWord right), encodeTable table], nativeCallMasks l r t state) := by
  have one := move_local_source (state := state) (slot := l) (value := .reference (encodeWord left)) (by rw [first]; simp only [Slot.materialize])
  have two := move_local_source (state := state.set l .empty) (slot := r) (value := .reference (encodeWord right))
    (by simp only [Partial.Locals.set, Ne.symm lr, ite_false, second, Slot.materialize])
  have three := move_local_source (state := (state.set l .empty).set r .empty) (slot := t) (value := encodeTable table)
    (by simp only [Partial.Locals.set, Ne.symm rt, Ne.symm lt, ite_false, third, Slot.materialize_ofValue])
  simp only [nativeCallArgs, SourceEval.operands, one, two, three, bind, Option.bind]
  rfl

theorem original_evaluator_call_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active)
    (l r t destination : Nat) (lr : l ≠ r) (lt : l ≠ t) (rt : r ≠ t)
    (dl : destination ≠ l) (dr : destination ≠ r) (dt : destination ≠ t) (outside : destination ∉ exceptions)
    (bounded : ∀ index ∈ exceptions, index < active.count)
    (left right : BalancedWord) (table : MemoTable) (childTotal : NativeTotal left right)
    (first : active.state l = .shared (encodeWord left)) (second : active.state r = .shared (encodeWord right))
    (third : active.state t = Slot.ofValue (encodeTable table)) {binding : Binding}
    (root : active.roots destination = some binding) (raw : world.memory[binding.address]? = some (.node .tuple 0 []))
    (empty : active.state destination = .empty) :
    ∃ minimumFuel minimumBudget final after result output cost,
      OriginalLoanMachine before callers previous external exceptions final after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      after.state = (nativeCallMasks l r t active.state).set destination (Slot.ofValue (encodeOutput result output)) ∧
      memoized_common_embedding left right table = .ok (result, output) ∧
      (∀ slot binding, slot ≠ destination → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Derived.call (Recursive.original budget fuel) world active callers .evaluate (nativeCallArgs l r t) destination = some (final, after, cost) := by
  have arguments := native_call_arguments l r t lr lt rt left right table first second third
  have emptyMasks : nativeCallMasks l r t active.state destination = .empty := by
    simpa only [nativeCallMasks, Partial.Locals.set, dl, dr, dt, ite_false] using empty
  have safe := ((h.native.safe.clear l).clear r).clear t
  have moves : ∀ current suspended, Scanned world active current → Callers world callers suspended →
      ∀ op ∈ nativeCallArgs l r t, Allowed world active.roots (current.loans ++ suspended.reads) op := by
    intro current suspended scanned callerView op member
    simp only [nativeCallArgs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact h.moves scanned callerView trivial
  have loans := Derived.RootLoansAllowed.of_safe_preserved (slot := destination) (active := {active with state := nativeCallMasks l r t active.state})
    safe raw (Or.inl rfl) h.native.previousCallers h.native.beforeWellFormed h.native.kept (h.native.fresh destination binding root)
  obtain ⟨fuel, budget, final, after, result, output, cost, state, native, _, _, _, _, _, stable⟩ :=
    Derived.evaluator_call_total h.native.valid h.native.callersValid h.native.wellFormed h.native.separate h.native.ownerFrame h.native.coverage
      left right table childTotal (nativeCallArgs l r t) root arguments emptyMasks moves loans
  have execute := (stable fuel budget (by rfl) (by rfl)).1
  have typed : SnapshotFieldsTyped [.reference (encodeWord left), .reference (encodeWord right), encodeTable table]
      [.shared (.adt .word), .shared (.adt .word), .adt .table] :=
    .cons (.shared (word_typed left)) (.cons (.shared (word_typed right)) (.cons (table_typed table) .nil))
  have outputType : Types.callOutput .evaluate [.shared (.adt .word), .shared (.adt .word), .adt .table] =
      some (.tuple [.adt .optional, .adt .table]) := by
    simp only [Types.callOutput, reduceCtorEq, ite_false, Types.inputs, SourceTypes.sameList_refl, ite_true, Types.output]
  have ready := Derived.call_ready_from_values (callers := callers) h.native.valid arguments typed outputType
  have checked := Derived.call_spec (Recursive.original_typed_respects budget fuel) h.native.valid h.native.callersValid h.native.wellFormed
    .evaluate (nativeCallArgs l r t) destination ready execute
  have original := h.advance_call (Recursive.original_typed_respects budget fuel) (Recursive.original_owns budget fuel)
    .evaluate (nativeCallArgs l r t) root outside ready arguments safe (((h.closed.clear l).clear r).clear t)
    (by intro index member
        by_cases one : index = l
        · subst index; right; simp [nativeCallMasks, Partial.Locals.set]
        by_cases two : index = r
        · subst index; right; simp [nativeCallMasks, Partial.Locals.set]
        by_cases three : index = t
        · subst index; right; simp [nativeCallMasks, Partial.Locals.set]
        · left; simp only [nativeCallMasks, Partial.Locals.set, one, two, three, ite_false])
    bounded (encodeOutput_typed result output) (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) state execute
  refine ⟨fuel, budget, final, after, result, output, cost, original, checked.2.2.2.1, checked.2.2.1, checked.2.1, state, native, ?_, ?_⟩
  · intro slot other different bound raw read
    have kept := Derived.call_preserves_other_root (Recursive.original_typed_respects budget fuel)
      h.native.valid h.native.callersValid h.native.wellFormed .evaluate (nativeCallArgs l r t) destination ready execute different bound
    exact kept.reads other.address (by simp) raw read
  · intro largerFuel largerBudget fuelBound budgetBound
    exact (stable largerFuel largerBudget fuelBound budgetBound).1

end SubtreeProofs.Rust.SourceEval.Evaluator
