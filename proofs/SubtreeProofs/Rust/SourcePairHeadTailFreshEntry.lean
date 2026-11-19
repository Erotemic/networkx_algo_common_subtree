module

public import SubtreeProofs.Rust.SourcePairTailFreshScope
public import SubtreeProofs.Rust.SourcePairHeadScopeEntry
public import SubtreeProofs.Rust.SourcePairTailScopeEntry

/-! Parsed pair/pair miss entry derives both head and tail witness owner
provenance from explicit stronger smaller contracts. All existing native scope,
result, query-alias and stable prefix guarantees are retained. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem entry_pair_head_scope_complete_fresh {world : World} {callers : List Activation} {previous : Resources}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (lh lt rh rt : BalancedWord) (table : MemoTable) (leftCell rightCell tableCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord (.Pair lh lt))))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord (.Pair rh rt))))
    (tableRead : Readable world.memory world.live tableCell (encodeTable table))
    {owners external : List Nat}
    (input : FieldsFootprint world.memory [leftCell, rightCell, tableCell] owners)
    (frame : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (miss : MemoizedOrderedSolver.findResult table (.Pair lh lt) (.Pair rh rt) = none) (childTotal : NativeTotalFresh lh rh) :
    let packets := inputPackets leftCell rightCell tableCell (.Pair lh lt) (.Pair rh rt) table
    ∃ entered active minimumFuel minimumBudget lookupWorld lookupActive missWorld missActive final after result output,
      enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount packets = some (entered, active) ∧
      MissScope active (.Pair lh lt) (.Pair rh rt) table missWorld missActive ∧
      OriginalLoanMachine world callers previous external [35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      PairHeadScope missActive lh lt rh rt result output final after ∧
      memoized_common_embedding lh rh table = .ok (result, output) ∧
      Derived.scrutinee final after callers (.discriminant (.local 31)) = some (lookupKey result, after) ∧
      LocalOwnersAbove world.memory.length final after 31 ∧
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
  obtain ⟨headFuel, headBudget, final, after, result, output, finalMachine, finalScope, native, fresh, stable⟩ :=
    pair_head_scope_complete_fresh (scope.original_machine machine closed queries tupleOrigin) scope unbound
      (by rw [scope.count, count]; decide) childTotal
  have inspection := Derived.scrutinee_complete finalMachine.native.valid finalMachine.native.callersValid _
    (head_result_scrutinee_source finalScope.result) (by intros; trivial)
  refine ⟨entered, active, max minFuel headFuel, max minBudget headBudget, lookupWorld, lookupActive, missWorld, missActive,
    final, after, result, output, entryRun, scope, finalMachine, finalScope, native, inspection, fresh, ?_⟩
  intro fuel budget fuelBound budgetBound
  obtain ⟨common, setup⟩ := prefixes fuel budget ((Nat.le_max_left _ _).trans fuelBound) ((Nat.le_max_left _ _).trans budgetBound)
  exact ⟨common, setup, stable fuel budget ((Nat.le_max_right _ _).trans fuelBound) ((Nat.le_max_right _ _).trans budgetBound)⟩


theorem entry_pair_tail_scope_complete_fresh {world : World} {callers : List Activation} {previous : Resources}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (lh lt rh rt : BalancedWord) (table afterHeads : MemoTable) (heads : CommonEmbedding) (leftCell rightCell tableCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord (.Pair lh lt))))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord (.Pair rh rt))))
    (tableRead : Readable world.memory world.live tableCell (encodeTable table))
    {owners external : List Nat}
    (input : FieldsFootprint world.memory [leftCell, rightCell, tableCell] owners)
    (frame : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (miss : MemoizedOrderedSolver.findResult table (.Pair lh lt) (.Pair rh rt) = none)
    (headsTotal : NativeTotalFresh lh rh) (tailsTotal : NativeTotalFresh lt rt)
    (headSuccess : memoized_common_embedding lh rh table = .ok (some heads, afterHeads)) :
    let packets := inputPackets leftCell rightCell tableCell (.Pair lh lt) (.Pair rh rt) table
    ∃ entered active minimumFuel minimumBudget lookupWorld lookupActive missWorld missActive headWorld headActive final after result output,
      enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount packets = some (entered, active) ∧
      PairHeadScope missActive lh lt rh rt (some heads) afterHeads headWorld headActive ∧
      OriginalLoanMachine world callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      PairTailScope headActive lh lt rh rt heads result output final after ∧
      Derived.scrutinee final after callers (.discriminant (.local 41)) = some (lookupKey result, after) ∧
      memoized_common_embedding lt rt afterHeads = .ok (result, output) ∧
      LocalOwnersAbove world.memory.length final after 37 ∧ LocalOwnersAbove world.memory.length final after 41 ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers lookupSwitch commonPrefix entered active lookupWorld lookupActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers missCases missSetupActions lookupWorld lookupActive missWorld missActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers headCases headActions missWorld missActive headWorld headActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers tailCases tailActions headWorld headActive final after := by
  dsimp only
  obtain ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive, resultH, outputH,
    entryRun, missScope, headMachine, headScope, headNative, inspection, headFresh, prefixes⟩ :=
    entry_pair_head_scope_complete_fresh hw hc view lh lt rh rt table leftCell rightCell tableCell leftRead rightRead tableRead
      input frame covered miss headsTotal
  obtain ⟨sameResult, sameOutput⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (headNative.symm.trans headSuccess))
  subst resultH
  subst outputH
  obtain ⟨sameWorld, sameActive, sameEntry, _, _, count, unbound, _⟩ :=
    native_entry_machine hw hc view (.Pair lh lt) (.Pair rh rt) table leftCell rightCell tableCell leftRead rightRead tableRead input frame covered
  have same := Prod.mk.inj (Option.some.inj (entryRun.symm.trans sameEntry))
  obtain ⟨rfl, rfl⟩ := same
  have support : ∀ slot, slot ∉ [0, 1, 2, 3, 13] → missActive.roots slot = none := by
    intro slot outside
    rw [missScope.otherRoots slot (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto)]
    exact unbound slot (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto)
  obtain ⟨tailFuel, tailBudget, final, after, result, output, machine, tailScope, native, headsKept, tailsFresh, stable⟩ :=
    pair_tail_scope_complete_fresh headMachine headScope support (by rw [headScope.count, missScope.count, count]; decide) tailsTotal headFresh
  have inspection := Derived.scrutinee_complete machine.native.valid machine.native.callersValid _
    (tail_result_scrutinee_source tailScope.result) (by intros; trivial)
  refine ⟨entered, active, max minFuel tailFuel, max minBudget tailBudget, lookupWorld, lookupActive, missWorld, missActive,
    headWorld, headActive, final, after, result, output, entryRun, headScope, machine, tailScope, inspection, native, headsKept, tailsFresh, ?_⟩
  intro fuel budget fuelBound budgetBound
  obtain ⟨common, setup, headPrefix⟩ := prefixes fuel budget ((Nat.le_max_left _ _).trans fuelBound) ((Nat.le_max_left _ _).trans budgetBound)
  exact ⟨common, setup, headPrefix, stable fuel budget ((Nat.le_max_right _ _).trans fuelBound) ((Nat.le_max_right _ _).trans budgetBound)⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
