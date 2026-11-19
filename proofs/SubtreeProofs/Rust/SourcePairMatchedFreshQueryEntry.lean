module

public import SubtreeProofs.Rust.SourcePairQueryScope
public import SubtreeProofs.Rust.SourcePairMatchedFreshEntry

/-! Exact native query snapshots accompany the constructed matched candidate.
Actual prefix determinism identifies the checked head checkpoint; raw mask
preservation transports its views through every later call and preparation. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem entry_pair_matched_queries_complete_fresh {world : World} {callers : List Activation} {previous : Resources}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (lh lt rh rt : BalancedWord) (table afterHeads output : MemoTable) (heads tails : CommonEmbedding)
    (subtotal total : Aeneas.Std.U32) (leftCell rightCell tableCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord (.Pair lh lt))))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord (.Pair rh rt))))
    (tableRead : Readable world.memory world.live tableCell (encodeTable table))
    {owners external : List Nat}
    (input : FieldsFootprint world.memory [leftCell, rightCell, tableCell] owners)
    (frame : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (miss : MemoizedOrderedSolver.findResult table (.Pair lh lt) (.Pair rh rt) = none)
    (headsTotal : NativeTotalFresh lh rh) (tailsTotal : NativeTotalFresh lt rt)
    (headSuccess : memoized_common_embedding lh rh table = .ok (some heads, afterHeads))
    (tailSuccess : memoized_common_embedding lt rt afterHeads = .ok (some tails, output))
    (subtotalSuccess : Aeneas.Std.U32.checked_add heads.edges tails.edges = some subtotal)
    (rootSuccess : Aeneas.Std.U32.checked_add subtotal 1#u32 = some total) :
    let packets := inputPackets leftCell rightCell tableCell (.Pair lh lt) (.Pair rh rt) table
    ∃ entered active minimumFuel minimumBudget lookupWorld lookupActive missWorld missActive headWorld headActive tailWorld tailActive scoreWorld scoreActive rootWorld rootActive final after,
      enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount packets = some (entered, active) ∧
      OriginalLoanMachine world callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      MatchedScope heads tails output total after ∧ PairQueryScope lh lt rh rt after ∧ after.count = CallingCertificate.originalEvaluator.source.localCount ∧
      (∀ slot ∈ [59, 61, 65, 66, 67, 68, 69, 70], after.roots slot = none) ∧
      (∀ slot ∈ [71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81], after.roots slot = none) ∧
      Derived.scrutinee rootWorld rootActive callers (.discriminant (.local 59)) = some (.variant .optional 1, rootActive) ∧
      LocalOwnersAbove world.memory.length final after 64 ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers lookupSwitch commonPrefix entered active lookupWorld lookupActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers missCases missSetupActions lookupWorld lookupActive missWorld missActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers headCases headActions missWorld missActive headWorld headActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers tailCases tailActions headWorld headActive tailWorld tailActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers scoreCases scoreActions tailWorld tailActive scoreWorld scoreActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers rootScoreCases rootScoreActions scoreWorld scoreActive rootWorld rootActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 30) (matchedActions.take 30) rootWorld rootActive final after := by
  dsimp only
  obtain ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive,
    tailWorld, tailActive, scoreWorld, scoreActive, rootWorld, rootActive, final, after,
    entryRun, machine, matchedScope, countAfter, retired, unbound, inspection, candidateFresh, prefixes⟩ :=
    entry_pair_matched_scope_complete_fresh hw hc view lh lt rh rt table afterHeads output heads tails subtotal total
      leftCell rightCell tableCell leftRead rightRead tableRead input frame covered miss headsTotal tailsTotal
      headSuccess tailSuccess subtotalSuccess rootSuccess
  obtain ⟨enteredH, activeH, fuelH, budgetH, lookupWorldH, lookupActiveH, missWorldH, missActiveH, headWorldH, headActiveH,
    resultH, outputH, entryH, missScopeH, headMachineH, headScopeH, nativeH, inspectionH, prefixesH⟩ :=
    entry_pair_head_scope_complete hw hc view lh lt rh rt table leftCell rightCell tableCell leftRead rightRead tableRead
      input frame covered miss headsTotal.total
  have sameEntry := Prod.mk.inj (Option.some.inj (entryRun.symm.trans entryH))
  obtain ⟨sameEntered, sameActive⟩ := sameEntry
  subst enteredH
  subst activeH
  let jointFuel := max minFuel fuelH
  let jointBudget := max minBudget budgetH
  obtain ⟨common, setup, head, tail, score, root, matched⟩ :=
    prefixes jointFuel jointBudget (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  obtain ⟨commonH, setupH, headH⟩ :=
    prefixesH jointFuel jointBudget (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  obtain ⟨sameLookupWorld, sameLookupActive⟩ := common.deterministic commonH
  subst lookupWorldH
  subst lookupActiveH
  obtain ⟨sameMissWorld, sameMissActive⟩ := setup.deterministic setupH
  subst missWorldH
  subst missActiveH
  obtain ⟨sameHeadWorld, sameHeadActive⟩ := head.deterministic headH
  subst headWorldH
  subst headActiveH
  have queries := (((headScopeH.query_scope.through_tail tail).through_score score).through_root_score root).through_matched matched
  refine ⟨entered, active, jointFuel, jointBudget, lookupWorld, lookupActive, missWorld, missActive,
    headWorld, headActive, tailWorld, tailActive, scoreWorld, scoreActive, rootWorld, rootActive, final, after,
    entryRun, machine, matchedScope, queries, countAfter, retired, unbound, inspection, candidateFresh, ?_⟩
  intro fuel budget fuelBound budgetBound
  exact prefixes fuel budget ((Nat.le_max_left _ _).trans fuelBound) ((Nat.le_max_left _ _).trans budgetBound)

end SubtreeProofs.Rust.SourceEval.Evaluator
