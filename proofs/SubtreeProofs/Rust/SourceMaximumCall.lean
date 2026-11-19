module

public import SubtreeProofs.Rust.SourceMaximumPreparation
public import SubtreeProofs.Rust.SourceOriginalEvaluatorCall
public import SubtreeProofs.Rust.SourceColdCallProvenance

/-! The actual public evaluator call is constructed from universal totality.
Its cold argument packet owns no old cells, so the complete stored tuple,
including the updated table, has fresh descendant owners. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Maximum

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem evaluate_call_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [5, 4, 1, 2] world active)
    (count : 7 ≤ active.count) (left right : BalancedWord)
    (first : active.state 4 = .shared (encodeWord left)) (second : active.state 5 = .shared (encodeWord right))
    (table : active.state 6 = Slot.ofValue (encodeTable .Empty))
    {binding : Binding} (root : active.roots 3 = some binding)
    (raw : world.memory[binding.address]? = some (.node .tuple 0 [])) (empty : active.state 3 = .empty) :
    ∃ minimumFuel minimumBudget final after result output cost,
      OriginalLoanMachine before callers previous external [5, 4, 1, 2] final after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      after.state 3 = Slot.ofValue (Evaluator.encodeOutput result output) ∧
      (∀ slot ∈ [4, 5, 6], after.state slot = .empty) ∧
      memoized_common_embedding left right .Empty = .ok (result, output) ∧
      LocalOwnersAbove before.memory.length final after 3 ∧
      (∀ slot other, slot ≠ 3 → active.roots slot = some other → ∀ cell,
        world.memory[other.address]? = some cell → final.memory[other.address]? = some cell) ∧
      (∀ slot, slot ∉ [3, 4, 5, 6] → (∀ value, active.state slot ≠ .shared value) → after.state slot = active.state slot) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.instruction (Recursive.original budget fuel) callers (world, active.forgetRefs callCode) evaluateCall =
          some ((final, after), cost) := by
  let observed := active.forgetRefs callCode
  have machine := h.prepare callCode
  have firstNow : observed.state 4 = .shared (encodeWord left) :=
    (Activation.forgetRefs_observed active callCode 4 (by decide +kernel)).trans first
  have secondNow : observed.state 5 = .shared (encodeWord right) :=
    (Activation.forgetRefs_observed active callCode 5 (by decide +kernel)).trans second
  have tableNow : observed.state 6 = Slot.ofValue (encodeTable .Empty) :=
    (h.prepare_closed_local callCode 6 (by decide)).trans table
  obtain ⟨fuel, budget, final, after, result, output, cost, original, roots, countEq, frameEq, state, native, memory, stable⟩ :=
    Evaluator.original_evaluator_call_complete machine 4 5 6 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by intro index member; change index < active.count
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega)
      left right .Empty (Evaluator.native_total left right) firstNow secondNow tableNow root raw
      (LoanEnding.forget_empty _ _ empty)
  have arguments := Evaluator.native_call_arguments 4 5 6 (by decide) (by decide) (by decide)
    left right .Empty firstNow secondNow tableNow
  have typed : SnapshotFieldsTyped [.reference (encodeWord left), .reference (encodeWord right), encodeTable .Empty]
      (Types.inputs .evaluate) :=
    .cons (.shared (word_typed left)) (.cons (.shared (word_typed right)) (.cons (table_typed .Empty) .nil))
  have out : Types.callOutput .evaluate (Types.inputs .evaluate) = some (Types.output .evaluate) := by
    simp only [Types.callOutput, reduceCtorEq, ite_false, SourceTypes.sameList_refl, ite_true]
  have ready := Derived.call_ready_from_values (callers := callers) machine.native.valid arguments typed out
  have fresh := Derived.original_call_fresh_output_of_no_input_owners fuel budget machine.native.valid
    machine.native.callersValid machine.native.wellFormed machine.native.ownerFrame machine.native.coverage
    (fun current suspended packets masks currentScan callerScan run => by
      have frame := (Activation.scan_spec machine.native.valid currentScan).frame
      obtain ⟨_, source, graph, included, _⟩ := Addressed.operands_spec frame _ run
      have same := Prod.mk.inj (Option.some.inj (source.symm.trans arguments))
      exact ⟨ready current suspended packets masks currentScan callerScan run,
        Evaluator.cold_packets_no_owners left right
          (Derived.packets_readable graph (fun address member => frame.alive address (included member))) same.1⟩)
    (stable fuel budget (by rfl) (by rfl))
  refine ⟨fuel, budget, final, after, result, output, cost, original, roots, countEq, frameEq, ?_, ?_, native,
    fresh.weaken h.native.memoryBound, memory, ?_, ?_⟩
  · simp only [state, Evaluator.nativeCallMasks, Partial.Locals.set, ite_true]
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp [state, Evaluator.nativeCallMasks, Partial.Locals.set]
  · intro slot outside unshared
    have h3 : slot ≠ 3 := by intro same; subst slot; simp at outside
    have h4 : slot ≠ 4 := by intro same; subst slot; simp at outside
    have h5 : slot ≠ 5 := by intro same; subst slot; simp at outside
    have h6 : slot ≠ 6 := by intro same; subst slot; simp at outside
    simp only [state, Evaluator.nativeCallMasks, Partial.Locals.set, h3, h4, h5, h6, ite_false]
    exact LoanEnding.forget_unshared callCode _ unshared
  · intro largerFuel largerBudget fuelBound budgetBound
    exact Calling.instruction_call_run (stable largerFuel largerBudget fuelBound budgetBound)

end SubtreeProofs.Rust.SourceEval.Maximum
