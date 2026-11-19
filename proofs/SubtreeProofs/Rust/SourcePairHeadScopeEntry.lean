module

public import SubtreeProofs.Rust.SourcePairHeadScope
public import SubtreeProofs.Rust.SourcePairHeadEntry

/-! Parsed native pair/pair miss entry through the actual head-result switch.
Complete scope/ownership and stable prefix machines are constructed from native
readable inputs and the smaller head request's explicit induction contract. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem head_result_scrutinee_source {state : State} {result : Option CommonEmbedding}
    (initialized : state 31 = Slot.ofValue (encodeOption result)) :
    SourceEval.scrutinee state (.discriminant (.local 31)) = some (lookupKey result, state) := by
  cases result <;> simp [SourceEval.scrutinee, splitPlace, initialized, encodeOption, Slot.ofValue, Slot.get, lookupKey]

theorem entry_pair_head_scope_complete {world : World} {callers : List Activation} {previous : Resources}
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
      PairHeadScope missActive lh lt rh rt result output final after ∧
      memoized_common_embedding lh rh table = .ok (result, output) ∧
      Derived.scrutinee final after callers (.discriminant (.local 31)) = some (lookupKey result, after) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers lookupSwitch commonPrefix entered active lookupWorld lookupActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers missCases missSetupActions lookupWorld lookupActive missWorld missActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers headCases headActions missWorld missActive final after := by
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
  obtain ⟨headFuel, headBudget, final, after, result, output, finalMachine, finalScope, native, stable⟩ :=
    pair_head_scope_complete (scope.original_machine machine closed queries tupleOrigin) scope unbound
      (by rw [scope.count, count]; decide) childTotal
  have inspection := Derived.scrutinee_complete finalMachine.native.valid finalMachine.native.callersValid _
    (head_result_scrutinee_source finalScope.result) (by intros; trivial)
  refine ⟨entered, active, max minFuel headFuel, max minBudget headBudget, lookupWorld, lookupActive, missWorld, missActive,
    final, after, result, output, entryRun, scope, finalMachine, finalScope, native, inspection, ?_⟩
  intro fuel budget fuelBound budgetBound
  obtain ⟨common, setup⟩ := prefixes fuel budget ((Nat.le_max_left _ _).trans fuelBound) ((Nat.le_max_left _ _).trans budgetBound)
  exact ⟨common, setup, stable fuel budget ((Nat.le_max_right _ _).trans fuelBound) ((Nat.le_max_right _ _).trans budgetBound)⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
