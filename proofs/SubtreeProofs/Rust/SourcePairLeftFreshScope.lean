module

public import SubtreeProofs.Rust.SourcePairLeftScope
public import SubtreeProofs.Rust.SourceCallOwnerProvenance

/-! Actual left recursion and eleven cleanup instructions derive witness
provenance while retaining the bounded matched candidate and owned left word. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_left_scope_complete_fresh {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat} {anchor : Resources}
    {lh lt rh rt : BalancedWord} {heads tails : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (h : AnchoredLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13]
      [77, 78] 71 (OrderedSolver.appendWord lh lt) anchor world active)
    (queries : PairQueryScope lh lt rh rt active) (candidate : MatchedScope heads tails table total active)
    (left : active.state 77 = .shared (encodeWord (OrderedSolver.appendWord lh lt)))
    (view78 : active.state 78 = .shared (encodeWord (OrderedSolver.appendWord lh lt)))
    (empty76 : active.state 76 = .empty)
    (root76 : ∃ binding, active.roots 76 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 []))
    (candidateAbove : LocalOwnersAbove before.memory.length world active 64)
    (wordAbove : LocalOwnersAbove before.memory.length world active 71)
    (count : 82 ≤ active.count) (unbound : ∀ slot ∈ [74, 75, 79, 80, 81], active.roots slot = none)
    (childTotal : NativeTotalFresh (OrderedSolver.appendWord lh lt) (.Pair rh rt)) :
    ∃ minimumFuel minimumBudget argumentWorld argumentActive callWorld callActive final after result output cost,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      PairLeftScope lh lt rh rt heads tails total result output final after ∧
      memoized_common_embedding (OrderedSolver.appendWord lh lt) (.Pair rh rt) table = .ok (result, output) ∧
      Derived.scrutinee final after callers (.discriminant (.local 74)) = some (lookupKey result, after) ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [74, 75, 76, 77, 78, 79, 80, 81] → after.roots slot = active.roots slot) ∧
      (∀ slot binding, slot ≠ 76 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      LocalOwnersAbove before.memory.length final after 74 ∧
      LocalOwnersAbove before.memory.length final after 64 ∧ LocalOwnersAbove before.memory.length final after 71 ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 48) ((matchedActions.drop 44).take 4) world active argumentWorld argumentActive ∧
        Derived.call (Recursive.original budget fuel) argumentWorld (argumentActive.forgetRefs (matchedCode 48)) callers
          .evaluate leftContractionArgs 76 = some (callWorld, callActive, cost) ∧
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 49) [.call .evaluate leftContractionArgs 76] argumentWorld argumentActive callWorld callActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers matchedCases ((matchedActions.drop 49).take 11) callWorld callActive final after ∧
        Calling.Prefix (Recursive.original budget fuel) callers matchedCases ((matchedActions.drop 44).take 16) world active final after := by
  obtain ⟨fuel, budget, argumentWorld, argumentActive, callWorld, callActive, final, after, result, output, cost,
    machine, scopeAfter, native, inspection, countAfter, frameAfter, rootsAfter, memoryAfter, stable⟩ :=
    pair_left_scope_complete h queries candidate left view78 empty76 root76 count unbound childTotal.total
  obtain ⟨arguments, called, callRun, cleanup, whole⟩ := stable fuel budget (by rfl) (by rfl)
  obtain ⟨checkedWorld, checkedActive, checkedArguments, checkedMachine, checkedScope, _, _, _, _, _⟩ :=
    pair_left_call_arguments_complete h (Recursive.original budget fuel) queries candidate left empty76 root76
      (by omega) (by
        intro slot member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> exact unbound _ (by simp))
  have candidateA := checkedArguments.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by decide +kernel))
    h.native.valid h.native.callersValid h.native.wellFormed candidateAbove
  have wordA := checkedArguments.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by decide +kernel))
    h.native.valid h.native.callersValid h.native.wellFormed wordAbove
  have same := checkedArguments.unique arguments
  have ma := checkedMachine
  have scopeA := checkedScope
  rw [same.1, same.2] at ma candidateA wordA
  rw [same.1, same.2] at scopeA
  let prepared := argumentActive.forgetRefs (matchedCode 48)
  have mp := ma.prepare (matchedCode 48)
  have first : prepared.state 77 = .shared (encodeWord (OrderedSolver.appendWord lh lt)) :=
    (Activation.forgetRefs_observed argumentActive (matchedCode 48) 77 (by decide +kernel)).trans scopeA.left
  have second : prepared.state 79 = .shared (encodeWord (.Pair rh rt)) :=
    (Activation.forgetRefs_observed argumentActive (matchedCode 48) 79 (by decide +kernel)).trans scopeA.right
  have third : prepared.state 80 = Slot.ofValue (encodeTable table) :=
    (LoanEnding.forget_closed _ _ (by rw [scopeA.tableValue]; exact ofValue_typed (table_typed table)) (.adt .table)).trans scopeA.tableValue
  have source := left_contraction_call_arguments (OrderedSolver.appendWord lh lt) (.Pair rh rt) table first second third
  obtain ⟨actualResult, actualTable, state, _, callValid, callersValid, callWellFormed, fresh⟩ :=
    Derived.evaluator_checkpoint_fresh_spec mp.native.valid mp.native.callersValid mp.native.wellFormed mp.native.ownerFrame mp.native.coverage
      (OrderedSolver.appendWord lh lt) (.Pair rh rt) table childTotal source called
  have typed : SnapshotFieldsTyped [.reference (encodeWord (OrderedSolver.appendWord lh lt)), .reference (encodeWord (.Pair rh rt)), encodeTable table]
      [.shared (.adt .word), .shared (.adt .word), .adt .table] :=
    .cons (.shared (word_typed _)) (.cons (.shared (word_typed _)) (.cons (table_typed table) .nil))
  have outputType : Types.callOutput .evaluate [.shared (.adt .word), .shared (.adt .word), .adt .table] =
      some (.tuple [.adt .optional, .adt .table]) := by
    simp only [Types.callOutput, reduceCtorEq, ite_false, Types.inputs, SourceTypes.sameList_refl, ite_true, Types.output]
  have ready := Derived.call_ready_from_values (callers := callers) mp.native.valid source typed outputType
  have candidateC := Derived.call_keeps_owner_provenance (Recursive.original_typed_respects budget fuel)
    mp.native.valid mp.native.callersValid mp.native.wellFormed ready
    (by change 64 < argumentActive.count; rw [arguments.shape.2.1]; omega) (by decide +kernel)
    (candidateA.prepare_any (matchedCode 48)) called
  have wordC := Derived.call_keeps_owner_provenance (Recursive.original_typed_respects budget fuel)
    mp.native.valid mp.native.callersValid mp.native.wellFormed ready
    (by change 71 < argumentActive.count; rw [arguments.shape.2.1]; omega) (by decide +kernel)
    (wordA.prepare_any (matchedCode 48)) called
  have candidateFinal := cleanup.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by decide +kernel))
    callValid callersValid callWellFormed candidateC
  have wordFinal := cleanup.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by decide +kernel))
    callValid callersValid callWellFormed wordC
  have value : callActive.state 76 = Slot.ofValue (encodeOutput actualResult actualTable) := by
    rw [state]; simp only [Partial.Locals.set, ite_true]
  have cleanupShape : Calling.Prefix (Recursive.original budget fuel) callers matchedCases
      ([80, 79, 77].map Action.storageDead ++
        ([.storageLive 74, .assign 74 (.use (.move (.field (.local 76) none 0)))] ++ (matchedActions.drop 54).take 6))
      callWorld callActive final after := cleanup
  have resultFresh := cleanupShape.retire_unpack_result_owner_provenance callValid callersValid callWellFormed
    (by decide) (by decide) value (fresh.weaken mp.native.memoryBound) (by decide +kernel) (by decide +kernel)
  exact ⟨fuel, budget, argumentWorld, argumentActive, callWorld, callActive, final, after, result, output, cost,
    machine, scopeAfter, native, inspection, countAfter, frameAfter, rootsAfter, memoryAfter, resultFresh, candidateFinal, wordFinal, stable⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
