module

public import SubtreeProofs.Rust.SourcePairHeadPrefix

/-! Parsed native entry, common lookup, miss setup and the sixteen actual
pair/pair head-prefix instructions execute at shared sufficient bounds. The
head result is native, and the only recursive premise concerns its strictly
smaller query pair. The subsequent branch and parent return remain separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem entry_pair_head_prefix_complete {world : World} {callers : List Activation} {previous : Resources}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (lh lt rh rt : BalancedWord) (table : MemoTable) (leftCell rightCell tableCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord (.Pair lh lt))))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord (.Pair rh rt))))
    (tableRead : Readable world.memory world.live tableCell (encodeTable table))
    {owners external : List Nat}
    (input : FieldsFootprint world.memory [leftCell, rightCell, tableCell] owners)
    (frame : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (miss : MemoizedOrderedSolver.findResult table (.Pair lh lt) (.Pair rh rt) = none) (childTotal : NativeTotal lh rh) :
    let packets := inputPackets leftCell rightCell tableCell (.Pair lh lt) (.Pair rh rt) table
    ∃ entered active minimumFuel minimumBudget lookupWorld lookupActive missWorld missActive final after result output,
      enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount packets = some (entered, active) ∧
      MissScope active (.Pair lh lt) (.Pair rh rt) table missWorld missActive ∧
      OriginalLoanMachine world callers previous external [35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.state 33 = Slot.ofValue (encodeOutput result output) ∧
      after.state 13 = queryTuple (.Pair lh lt) (.Pair rh rt) ∧
      memoized_common_embedding lh rh table = .ok (result, output) ∧
      Derived.scrutinee missWorld missActive callers (.discriminant (.deref (.field (.local 13) none 0))) =
        some (.variant .word 1, missActive) ∧
      Derived.scrutinee missWorld missActive callers (.discriminant (.deref (.field (.local 13) none 1))) =
        some (.variant .word 1, missActive) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers lookupSwitch commonPrefix entered active lookupWorld lookupActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers missCases missSetupActions lookupWorld lookupActive missWorld missActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (headCode 16) (headActions.take 16) missWorld missActive final after := by
  dsimp only
  obtain ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, entryRun, unbound,
    machine, scope, queries, tupleOrigin, closed, words, lookupInspection, inspectLeft, inspectRight, prefixes⟩ :=
    entry_miss_setup_complete hw hc view (.Pair lh lt) (.Pair rh rt) table leftCell rightCell tableCell
      leftRead rightRead tableRead input frame covered miss
  obtain ⟨sameWorld, sameActive, sameEntry, _, _, count, _, _⟩ :=
    native_entry_machine hw hc view (.Pair lh lt) (.Pair rh rt) table leftCell rightCell tableCell
      leftRead rightRead tableRead input frame covered
  have same := Prod.mk.inj (Option.some.inj (entryRun.symm.trans sameEntry))
  obtain ⟨rfl, rfl⟩ := same
  obtain ⟨headFuel, headBudget, final, after, result, output, finalMachine, _, _, value, tuple, _, _, _, _, _, _, _, _, native, _, _, _, _, stable⟩ :=
    pair_head_prefix_complete (scope.original_machine machine closed queries tupleOrigin) scope unbound
      (by rw [scope.count, count]; decide) childTotal
  refine ⟨entered, active, max minFuel headFuel, max minBudget headBudget, lookupWorld, lookupActive, missWorld, missActive,
    final, after, result, output, entryRun, scope, finalMachine, value, tuple, native, inspectLeft, inspectRight, ?_⟩
  intro fuel budget fuelBound budgetBound
  obtain ⟨common, setup⟩ := prefixes fuel budget ((Nat.le_max_left _ _).trans fuelBound) ((Nat.le_max_left _ _).trans budgetBound)
  exact ⟨common, setup, stable fuel budget ((Nat.le_max_right _ _).trans fuelBound) ((Nat.le_max_right _ _).trans budgetBound)⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
