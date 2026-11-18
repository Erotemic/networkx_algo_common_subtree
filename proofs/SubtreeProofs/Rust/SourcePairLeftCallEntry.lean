module

public import SubtreeProofs.Rust.SourcePairLeftCallPrefix

/-! Parsed evaluator entry reaches the actual left contraction return under
explicit contracts for smaller head, tail and concatenated-left requests. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem entry_pair_left_call_complete {world : World} {callers : List Activation} {previous : Resources}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (lh lt rh rt : BalancedWord) (table afterHeads afterTails : MemoTable) (heads tails : CommonEmbedding)
    (subtotal total : Aeneas.Std.U32) (leftCell rightCell tableCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord (.Pair lh lt))))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord (.Pair rh rt))))
    (tableRead : Readable world.memory world.live tableCell (encodeTable table))
    {owners external : List Nat}
    (input : FieldsFootprint world.memory [leftCell, rightCell, tableCell] owners)
    (frame : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (miss : MemoizedOrderedSolver.findResult table (.Pair lh lt) (.Pair rh rt) = none)
    (headsTotal : NativeTotal lh rh) (tailsTotal : NativeTotal lt rt)
    (headSuccess : memoized_common_embedding lh rh table = .ok (some heads, afterHeads))
    (tailSuccess : memoized_common_embedding lt rt afterHeads = .ok (some tails, afterTails))
    (subtotalSuccess : Aeneas.Std.U32.checked_add heads.edges tails.edges = some subtotal)
    (rootSuccess : Aeneas.Std.U32.checked_add subtotal 1#u32 = some total)
    (leftTotal : NativeTotal (OrderedSolver.appendWord lh lt) (.Pair rh rt)) :
    let packets := inputPackets leftCell rightCell tableCell (.Pair lh lt) (.Pair rh rt) table
    ∃ entered active minimumFuel minimumBudget lookupWorld lookupActive missWorld missActive headWorld headActive tailWorld tailActive scoreWorld scoreActive rootWorld rootActive matchedWorld matchedActive concatWorld concatActive viewsWorld viewsActive argumentWorld argumentActive final after anchor result output cost,
      enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount packets = some (entered, active) ∧
      AnchoredLoanMachine world callers previous external [79, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13]
        [77, 78] 71 (OrderedSolver.appendWord lh lt) anchor final after ∧
      MatchedCandidateScope heads tails total after ∧ PairQueryScope lh lt rh rt after ∧
      after.state 71 = Slot.ofValue (encodeWord (OrderedSolver.appendWord lh lt)) ∧
      after.state 76 = Slot.ofValue (encodeOutput result output) ∧ after.state 42 = .empty ∧
      (∀ slot ∈ [77, 79, 80], after.state slot = .empty) ∧
      memoized_common_embedding (OrderedSolver.appendWord lh lt) (.Pair rh rt) afterTails = .ok (result, output) ∧
      after.count = CallingCertificate.originalEvaluator.source.localCount ∧
      (∀ slot ∈ [74, 75, 81], after.roots slot = none) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers lookupSwitch commonPrefix entered active lookupWorld lookupActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers missCases missSetupActions lookupWorld lookupActive missWorld missActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers headCases headActions missWorld missActive headWorld headActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers tailCases tailActions headWorld headActive tailWorld tailActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers scoreCases scoreActions tailWorld tailActive scoreWorld scoreActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers rootScoreCases rootScoreActions scoreWorld scoreActive rootWorld rootActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 30) (matchedActions.take 30) rootWorld rootActive matchedWorld matchedActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 39) ((matchedActions.drop 30).take 9) matchedWorld matchedActive concatWorld concatActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 44) ((matchedActions.drop 39).take 5) concatWorld concatActive viewsWorld viewsActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 48) ((matchedActions.drop 44).take 4) viewsWorld viewsActive argumentWorld argumentActive ∧
        Derived.call (Recursive.original budget fuel) argumentWorld (argumentActive.forgetRefs (matchedCode 48)) callers
          .evaluate leftContractionArgs 76 = some (final, after, cost) ∧
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 49) [.call .evaluate leftContractionArgs 76] argumentWorld argumentActive final after := by
  dsimp only
  obtain ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive,
    tailWorld, tailActive, scoreWorld, scoreActive, rootWorld, rootActive, matchedWorld, matchedActive, concatWorld, concatActive,
    viewsWorld, viewsActive, anchor, _, _, entryRun, machine, candidate, queries, _, left, _, empty76, root76,
    count, unbound, _, _, prefixes⟩ :=
    entry_pair_left_word_views_complete hw hc view lh lt rh rt table afterHeads afterTails heads tails subtotal total
      leftCell rightCell tableCell leftRead rightRead tableRead input frame covered miss headsTotal tailsTotal
      headSuccess tailSuccess subtotalSuccess rootSuccess
  obtain ⟨leftFuel, leftBudget, argumentWorld, argumentActive, final, after, result, output, cost, finalMachine, finalQueries, finalCandidate,
    resultValue, tableMoved, moved, native, countAfter, _, rootsAfter, _, stable⟩ :=
    pair_left_call_prefix_complete machine queries candidate left empty76 root76
      (by rw [count, (CallingCertificate.originalEvaluator_spec).2.1]; decide)
      (by intro slot member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl <;> exact unbound _ (by simp)) leftTotal
  refine ⟨entered, active, max minFuel leftFuel, max minBudget leftBudget,
    lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive, tailWorld, tailActive, scoreWorld, scoreActive,
    rootWorld, rootActive, matchedWorld, matchedActive, concatWorld, concatActive, viewsWorld, viewsActive,
    argumentWorld, argumentActive, final, after, anchor, result, output, cost, entryRun, finalMachine, finalCandidate, finalQueries, finalMachine.value,
    resultValue, tableMoved, moved, native, countAfter.trans count, ?_, ?_⟩
  · intro slot member
    have outside : slot ∉ [79, 80] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide
    rw [rootsAfter slot outside]
    exact unbound slot (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      rcases member with rfl | rfl | rfl <;> simp)
  · intro fuel budget fuelBound budgetBound
    obtain ⟨common, setup, head, tail, score, root, matched, concat, views⟩ :=
      prefixes fuel budget ((Nat.le_max_left _ _).trans fuelBound) ((Nat.le_max_left _ _).trans budgetBound)
    obtain ⟨arguments, callRun, callPrefix, _⟩ :=
      stable fuel budget ((Nat.le_max_right _ _).trans fuelBound) ((Nat.le_max_right _ _).trans budgetBound)
    exact ⟨common, setup, head, tail, score, root, matched, concat, views, arguments, callRun, callPrefix⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
