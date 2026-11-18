module

public import SubtreeProofs.Rust.SourceOriginalCheckedAdd

/-! Construct actual concatenation from original shared word views. Typed
helper totality and the independent source refinement identify the appended
native word, structural event profile and stable complete checked call. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def concatenateArgs (left right : Nat) : List Operand := [.move (.local left), .move (.local right)]

theorem concatenate_arguments_source {state : State} (l r : Nat) (different : l ≠ r) (left right : BalancedWord)
    (first : state l = .shared (encodeWord left)) (second : state r = .shared (encodeWord right)) :
    SourceEval.operands state (concatenateArgs l r) =
      some ([.reference (encodeWord left), .reference (encodeWord right)], (state.set l .empty).set r .empty) := by
  have one := move_local_source (state := state) (slot := l) (value := .reference (encodeWord left)) (by rw [first]; simp only [Slot.materialize])
  have two := move_local_source (state := state.set l .empty) (slot := r) (value := .reference (encodeWord right))
    (by simp only [Partial.Locals.set, Ne.symm different, ite_false, second, Slot.materialize])
  simp only [concatenateArgs, SourceEval.operands, one, two, bind, Option.bind]

theorem original_concatenate_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active)
    (l r destination : Nat) (lr : l ≠ r) (dl : destination ≠ l) (dr : destination ≠ r)
    (outside : destination ∉ exceptions) (bounded : ∀ index ∈ exceptions, index < active.count)
    (left right : BalancedWord) (first : active.state l = .shared (encodeWord left)) (second : active.state r = .shared (encodeWord right))
    {binding : Binding} (root : active.roots destination = some binding)
    (raw : world.memory[binding.address]? = some (.node .tuple 0 [])) (empty : active.state destination = .empty) :
    ∃ minimumFuel minimumBudget final after, ∃ cost : Cost, ∃ nativeCost : LookupSource.Cost,
      OriginalLoanMachine before callers previous external exceptions final after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      after.state = ((active.state.set l .empty).set r .empty).set destination
        (Slot.ofValue (encodeWord (OrderedSolver.appendWord left right))) ∧
      nativeCost.events = MemoSource.concatenateEvents left right ∧
      cost = (Cost.local (Action.call .concatenate (concatenateArgs l r) destination).weight).plus (SourceEval.Legacy.costMap nativeCost) ∧
      (∀ slot binding, slot ≠ destination → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Derived.call (Recursive.original budget fuel) world active callers .concatenate (concatenateArgs l r) destination = some (final, after, cost) := by
  have arguments := concatenate_arguments_source l r lr left right first second
  have emptyMasks : ((active.state.set l .empty).set r .empty) destination = .empty := by
    simpa only [Partial.Locals.set, dl, dr, ite_false] using empty
  have safe := (h.native.safe.clear l).clear r
  have moves : ∀ current suspended, Scanned world active current → Callers world callers suspended →
      ∀ op ∈ concatenateArgs l r, Allowed world active.roots (current.loans ++ suspended.reads) op := by
    intro current suspended scanned callerView op member
    simp only [concatenateArgs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact h.moves scanned callerView trivial
  have loans := Derived.RootLoansAllowed.of_safe_preserved (slot := destination)
    (active := {active with state := (active.state.set l .empty).set r .empty}) safe raw (Or.inl rfl)
    h.native.previousCallers h.native.beforeWellFormed h.native.kept (h.native.fresh destination binding root)
  have typed : SnapshotFieldsTyped [.reference (encodeWord left), .reference (encodeWord right)] [.shared (.adt .word), .shared (.adt .word)] :=
    .cons (.shared (word_typed left)) (.cons (.shared (word_typed right)) .nil)
  have outputType : Types.callOutput .concatenate [.shared (.adt .word), .shared (.adt .word)] = some (.adt .word) := by
    simp only [Types.callOutput, reduceCtorEq, ite_false, Types.inputs, SourceTypes.sameList_refl, ite_true, Types.output]
  obtain ⟨minFuel, minBudget, final, after, cost, _, _, _, _, _, stable⟩ :=
    Recursive.original_helper_call_stable h.native.valid h.native.callersValid h.native.wellFormed h.native.separate
      h.native.ownerFrame h.native.coverage .concatenate rfl (concatenateArgs l r) root arguments emptyMasks typed outputType (.adt .word) moves loans
  let sufficient := max minFuel (MemoSource.concatenateDepth left right)
  have execute := (stable sufficient minBudget (Nat.le_max_left _ _) (by rfl)).1
  have source := (stable sufficient minBudget (Nat.le_max_left _ _) (by rfl)).2
  obtain ⟨nativeCost, nativeRun, events⟩ := SourceEval.Helpers.concatenate_source left right sufficient (Nat.le_max_right _ _)
  rw [SourceEval.action, arguments] at source
  simp only [bind, Option.bind] at source
  rw [nativeRun] at source
  have same := Prod.mk.inj (Option.some.inj source)
  have state := same.1.symm
  have costEq := same.2.symm
  have ready := Derived.call_ready_from_values (callers := callers) h.native.valid arguments typed outputType
  have checked := Derived.call_spec (Recursive.original_typed_respects minBudget sufficient)
    h.native.valid h.native.callersValid h.native.wellFormed .concatenate (concatenateArgs l r) destination ready execute
  have original := h.advance_call (Recursive.original_typed_respects minBudget sufficient) (Recursive.original_owns minBudget sufficient)
    .concatenate (concatenateArgs l r) root outside ready arguments safe ((h.closed.clear l).clear r)
    (by intro index member
        by_cases one : index = l
        · subst index; right; simp [Partial.Locals.set]
        by_cases two : index = r
        · subst index; right; simp [Partial.Locals.set]
        · left; simp only [Partial.Locals.set, one, two, ite_false])
    bounded (word_typed (OrderedSolver.appendWord left right)) (.adt .word) state execute
  refine ⟨sufficient, minBudget, final, after, cost, nativeCost, original, checked.2.2.2.1, checked.2.2.1, checked.2.1, state, events, costEq, ?_, ?_⟩
  · intro slot other notDestination bound raw memoryRead
    have kept := Derived.call_preserves_other_root (Recursive.original_typed_respects minBudget sufficient)
      h.native.valid h.native.callersValid h.native.wellFormed .concatenate (concatenateArgs l r) destination ready execute notDestination bound
    exact kept.reads other.address (by simp) raw memoryRead
  · intro fuel budget fuelBound budgetBound
    exact (stable fuel budget ((Nat.le_max_left _ _).trans fuelBound) budgetBound).1

end SubtreeProofs.Rust.SourceEval.Evaluator
