module

public import SubtreeProofs.Rust.SourcePairRightFreshScope
public import SubtreeProofs.Rust.SourceCallOwnerProvenance

/-! The complete actual right recursive region retains the candidate, left
witness and both owned words while deriving the right optional witness bound. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_right_scope_complete_provenance {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat} {anchor : Resources}
    {lh lt rh rt : BalancedWord} {heads tails leftWitness : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (h : AnchoredLoanMachine before callers previous external [91, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13]
      [92, 93] 85 (OrderedSolver.appendWord rh rt) anchor world active)
    (scope : RightConcatScope lh lt rh rt heads tails leftWitness table total active)
    (leftView : active.state 91 = .shared (encodeWord (.Pair lh lt)))
    (rightView : active.state 92 = .shared (encodeWord (OrderedSolver.appendWord rh rt)))
    (view93 : active.state 93 = .shared (encodeWord (OrderedSolver.appendWord rh rt)))
    (empty90 : active.state 90 = .empty)
    (root90 : ∃ binding, active.roots 90 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 []))
    (heldAbove : ∀ slot ∈ [64, 71, 81, 85], LocalOwnersAbove before.memory.length world active slot)
    (count : 96 ≤ active.count) (unbound : ∀ slot ∈ [88, 89, 94, 95], active.roots slot = none)
    (childTotal : NativeTotalFresh (.Pair lh lt) (OrderedSolver.appendWord rh rt)) :
    ∃ minimumFuel minimumBudget argumentWorld argumentActive callWorld callActive final after result output cost,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      PairRightScope lh lt rh rt heads tails leftWitness total result output final after ∧
      memoized_common_embedding (.Pair lh lt) (OrderedSolver.appendWord rh rt) table = .ok (result, output) ∧
      Derived.scrutinee final after callers (.discriminant (.local 88)) = some (lookupKey result, after) ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [88, 89, 90, 91, 93, 92, 94, 95] → after.roots slot = active.roots slot) ∧
      (∀ slot binding, slot ≠ 90 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      LocalOwnersAbove before.memory.length final after 88 ∧
      (∀ slot ∈ [64, 71, 81, 85], LocalOwnersAbove before.memory.length final after slot) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers (rightCode 24) ((rightActions.drop 22).take 2) world active argumentWorld argumentActive ∧
        Derived.call (Recursive.original budget fuel) argumentWorld (argumentActive.forgetRefs (rightCode 24)) callers
          .evaluate rightContractionArgs 90 = some (callWorld, callActive, cost) ∧
        Calling.Prefix (Recursive.original budget fuel) callers (rightCode 25) [.call .evaluate rightContractionArgs 90] argumentWorld argumentActive callWorld callActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers rightContractionCases ((rightActions.drop 25).take 11) callWorld callActive final after ∧
        Calling.Prefix (Recursive.original budget fuel) callers rightContractionCases ((rightActions.drop 22).take 14) world active final after := by
  obtain ⟨fuel, budget, argumentWorld, argumentActive, callWorld, callActive, final, after, result, output, cost,
    machine, scopeAfter, native, inspection, countAfter, frameAfter, rootsAfter, memoryAfter, stable⟩ :=
    pair_right_scope_complete h scope leftView rightView view93 empty90 root90 count unbound childTotal.total
  obtain ⟨arguments, called, callRun, cleanup, whole⟩ := stable fuel budget (by rfl) (by rfl)
  obtain ⟨checkedWorld, checkedActive, checkedArguments, checkedMachine, checkedScope, _, _, _, _, _⟩ :=
    pair_right_call_arguments_complete h (Recursive.original budget fuel) scope.payload leftView rightView empty90 root90
      (by omega) (unbound 94 (by simp))
  have heldA : ∀ slot ∈ [64, 71, 81, 85], LocalOwnersAbove before.memory.length checkedWorld checkedActive slot := by
    intro slot member
    exact checkedArguments.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide +kernel))
      h.native.valid h.native.callersValid h.native.wellFormed (heldAbove slot member)
  have same := checkedArguments.unique arguments
  have ma := checkedMachine
  rw [same.1, same.2] at ma heldA
  have scopeA := checkedScope
  rw [same.1, same.2] at scopeA
  let prepared := argumentActive.forgetRefs (rightCode 24)
  have mp := ma.prepare (rightCode 24)
  have first : prepared.state 91 = .shared (encodeWord (.Pair lh lt)) :=
    (Activation.forgetRefs_observed argumentActive (rightCode 24) 91 (by decide +kernel)).trans scopeA.left
  have second : prepared.state 92 = .shared (encodeWord (OrderedSolver.appendWord rh rt)) :=
    (Activation.forgetRefs_observed argumentActive (rightCode 24) 92 (by decide +kernel)).trans scopeA.right
  have third : prepared.state 94 = Slot.ofValue (encodeTable table) :=
    (LoanEnding.forget_closed _ _ (by rw [scopeA.tableValue]; exact ofValue_typed (table_typed table)) (.adt .table)).trans scopeA.tableValue
  have source := right_contraction_call_arguments (.Pair lh lt) (OrderedSolver.appendWord rh rt) table first second third
  obtain ⟨actualResult, actualTable, state, _, callValid, callersValid, callWellFormed, fresh⟩ :=
    Derived.evaluator_checkpoint_fresh_spec mp.native.valid mp.native.callersValid mp.native.wellFormed mp.native.ownerFrame mp.native.coverage
      (.Pair lh lt) (OrderedSolver.appendWord rh rt) table childTotal source called
  have typed : SnapshotFieldsTyped [.reference (encodeWord (.Pair lh lt)), .reference (encodeWord (OrderedSolver.appendWord rh rt)), encodeTable table]
      [.shared (.adt .word), .shared (.adt .word), .adt .table] :=
    .cons (.shared (word_typed _)) (.cons (.shared (word_typed _)) (.cons (table_typed table) .nil))
  have outputType : Types.callOutput .evaluate [.shared (.adt .word), .shared (.adt .word), .adt .table] =
      some (.tuple [.adt .optional, .adt .table]) := by
    simp only [Types.callOutput, reduceCtorEq, ite_false, Types.inputs, SourceTypes.sameList_refl, ite_true, Types.output]
  have ready := Derived.call_ready_from_values (callers := callers) mp.native.valid source typed outputType
  have heldFinal : ∀ slot ∈ [64, 71, 81, 85], LocalOwnersAbove before.memory.length final after slot := by
    intro slot member
    have slotBound : slot < argumentActive.count := by
      rw [arguments.shape.2.1]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> omega
    have safe : LocalPreservation.action slot (.call .evaluate rightContractionArgs 90) = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide +kernel
    have kept := Derived.call_keeps_owner_provenance (Recursive.original_typed_respects budget fuel)
      mp.native.valid mp.native.callersValid mp.native.wellFormed ready slotBound safe
      ((heldA slot member).prepare_any (rightCode 24)) called
    exact cleanup.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide +kernel)) callValid callersValid callWellFormed kept
  have value : callActive.state 90 = Slot.ofValue (encodeOutput actualResult actualTable) := by
    rw [state]; simp only [Partial.Locals.set, ite_true]
  have selected : LocalResultOwnersAbove before.memory.length callWorld callActive 90 := fresh.weaken mp.native.memoryBound
  have cleanupShape : Calling.Prefix (Recursive.original budget fuel) callers rightContractionCases
      ([94, 92, 91].map Action.storageDead ++
        ([.storageLive 88, .assign 88 (.use (.move (.field (.local 90) none 0)))] ++ (rightActions.drop 30).take 6))
      callWorld callActive final after := cleanup
  have outputFresh := cleanupShape.retire_unpack_result_owner_provenance callValid callersValid callWellFormed
    (by decide) (by decide) value selected (by decide +kernel) (by decide +kernel)
  exact ⟨fuel, budget, argumentWorld, argumentActive, callWorld, callActive, final, after, result, output, cost,
    machine, scopeAfter, native, inspection, countAfter, frameAfter, rootsAfter, memoryAfter, outputFresh, heldFinal, stable⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
