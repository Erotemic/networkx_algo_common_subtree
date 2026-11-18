module

public import SubtreeProofs.Rust.SourcePairLeftConcatFreshScope
public import SubtreeProofs.Rust.SourcePairMatchedFreshQueryEntry

/-! Parsed evaluator entry reaches the owned left contraction query through
all eight stable actual prefix boundaries, retaining original query snapshots. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem entry_pair_left_concat_scope_complete_fresh {world : World} {callers : List Activation} {previous : Resources}
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
    ∃ entered active minimumFuel minimumBudget lookupWorld lookupActive missWorld missActive headWorld headActive tailWorld tailActive scoreWorld scoreActive rootWorld rootActive matchedWorld matchedActive final after,
    ∃ cost : Cost, ∃ nativeCost : LookupSource.Cost,
      enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount packets = some (entered, active) ∧
      OriginalLoanMachine world callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      MatchedScope heads tails output total after ∧ PairQueryScope lh lt rh rt after ∧
      after.state 71 = Slot.ofValue (encodeWord (OrderedSolver.appendWord lh lt)) ∧
      (∃ binding, after.roots 71 = some binding) ∧ after.count = CallingCertificate.originalEvaluator.source.localCount ∧
      (∀ slot ∈ [59, 61, 65, 66, 67, 68, 69, 70, 72, 73], after.roots slot = none) ∧
      (∀ slot ∈ [74, 75, 76, 77, 78, 79, 80, 81], after.roots slot = none) ∧
      nativeCost.events = MemoSource.concatenateEvents lh lt ∧
      cost = (Cost.local (Action.call .concatenate (concatenateArgs 72 73) 71).weight).plus (SourceEval.Legacy.costMap nativeCost) ∧
      Derived.scrutinee rootWorld rootActive callers (.discriminant (.local 59)) = some (.variant .optional 1, rootActive) ∧
      LocalOwnersAbove world.memory.length final after 64 ∧ LocalOwnersAbove world.memory.length final after 71 ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers lookupSwitch commonPrefix entered active lookupWorld lookupActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers missCases missSetupActions lookupWorld lookupActive missWorld missActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers headCases headActions missWorld missActive headWorld headActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers tailCases tailActions headWorld headActive tailWorld tailActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers scoreCases scoreActions tailWorld tailActive scoreWorld scoreActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers rootScoreCases rootScoreActions scoreWorld scoreActive rootWorld rootActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 30) (matchedActions.take 30) rootWorld rootActive matchedWorld matchedActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 39) ((matchedActions.drop 30).take 9) matchedWorld matchedActive final after := by
  dsimp only
  obtain ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive,
    tailWorld, tailActive, scoreWorld, scoreActive, rootWorld, rootActive, matchedWorld, matchedActive,
    entryRun, machine, matchedScope, queries, count, retired, unbound, inspection, candidateFresh, prefixes⟩ :=
    entry_pair_matched_queries_complete_fresh hw hc view lh lt rh rt table afterHeads output heads tails subtotal total
      leftCell rightCell tableCell leftRead rightRead tableRead input frame covered miss headsTotal tailsTotal
      headSuccess tailSuccess subtotalSuccess rootSuccess
  obtain ⟨concatFuel, concatBudget, final, after, cost, nativeCost, finalMachine, finalQueries, finalCandidate, value, bound,
    dead72, dead73, countAfter, _, rootsAfter, events, costEq, _, candidateFinal, wordFinal, stable⟩ :=
    pair_left_concat_scope_complete_fresh machine queries matchedScope candidateFresh
      (by rw [count, (CallingCertificate.originalEvaluator_spec).2.1]; decide)
      (by intro slot member; exact unbound slot (List.mem_append_left [74, 75, 76, 77, 78, 79, 80, 81] member))
  refine ⟨entered, active, max minFuel concatFuel, max minBudget concatBudget,
    lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive, tailWorld, tailActive,
    scoreWorld, scoreActive, rootWorld, rootActive, matchedWorld, matchedActive, final, after, cost, nativeCost,
    entryRun, finalMachine, finalCandidate, finalQueries, value, bound, countAfter.trans count, ?_, ?_, events, costEq, inspection, candidateFinal, wordFinal, ?_⟩
  · intro slot member
    have selected : slot ∈ [59, 61, 65, 66, 67, 68, 69, 70] ∨ slot = 72 ∨ slot = 73 := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] using member
    rcases selected with old | rfl | rfl
    · rw [rootsAfter slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at old ⊢; rcases old with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
      exact retired slot old
    · exact dead72
    · exact dead73
  · intro slot member
    have outside : slot ∉ [71, 72, 73] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [rootsAfter slot outside]
    exact unbound slot (List.mem_append_right [71, 72, 73] member)
  · intro fuel budget fuelBound budgetBound
    obtain ⟨common, setup, head, tail, score, root, matched⟩ :=
      prefixes fuel budget ((Nat.le_max_left _ _).trans fuelBound) ((Nat.le_max_left _ _).trans budgetBound)
    exact ⟨common, setup, head, tail, score, root, matched,
      stable fuel budget ((Nat.le_max_right _ _).trans fuelBound) ((Nat.le_max_right _ _).trans budgetBound)⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
