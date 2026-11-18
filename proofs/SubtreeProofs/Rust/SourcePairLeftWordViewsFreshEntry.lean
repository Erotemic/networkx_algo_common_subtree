module

public import SubtreeProofs.Rust.SourcePairLeftWordViews
public import SubtreeProofs.Rust.SourcePairLeftConcatFreshEntry

/-! Parsed entry reaches both actual fresh left-query views. Their loans are
anchored in the owned concatenated word, separately from original query loans. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem entry_pair_left_word_views_complete_fresh {world : World} {callers : List Activation} {previous : Resources}
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
    ∃ entered active minimumFuel minimumBudget lookupWorld lookupActive missWorld missActive headWorld headActive tailWorld tailActive scoreWorld scoreActive rootWorld rootActive matchedWorld matchedActive concatWorld concatActive final after anchor,
    ∃ cost : Cost, ∃ nativeCost : LookupSource.Cost,
      enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount packets = some (entered, active) ∧
      AnchoredLoanMachine world callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13]
        [77, 78] 71 (OrderedSolver.appendWord lh lt) anchor final after ∧
      MatchedScope heads tails output total after ∧ PairQueryScope lh lt rh rt after ∧
      after.state 71 = Slot.ofValue (encodeWord (OrderedSolver.appendWord lh lt)) ∧
      after.state 77 = .shared (encodeWord (OrderedSolver.appendWord lh lt)) ∧
      after.state 78 = .shared (encodeWord (OrderedSolver.appendWord lh lt)) ∧
      after.state 76 = .empty ∧
      (∃ binding, after.roots 76 = some binding ∧ final.memory[binding.address]? = some (.node .tuple 0 [])) ∧
      after.count = CallingCertificate.originalEvaluator.source.localCount ∧
      (∀ slot ∈ [74, 75, 79, 80, 81], after.roots slot = none) ∧
      nativeCost.events = MemoSource.concatenateEvents lh lt ∧
      cost = (Cost.local (Action.call .concatenate (concatenateArgs 72 73) 71).weight).plus (SourceEval.Legacy.costMap nativeCost) ∧
      LocalOwnersAbove world.memory.length final after 64 ∧ LocalOwnersAbove world.memory.length final after 71 ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers lookupSwitch commonPrefix entered active lookupWorld lookupActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers missCases missSetupActions lookupWorld lookupActive missWorld missActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers headCases headActions missWorld missActive headWorld headActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers tailCases tailActions headWorld headActive tailWorld tailActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers scoreCases scoreActions tailWorld tailActive scoreWorld scoreActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers rootScoreCases rootScoreActions scoreWorld scoreActive rootWorld rootActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 30) (matchedActions.take 30) rootWorld rootActive matchedWorld matchedActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 39) ((matchedActions.drop 30).take 9) matchedWorld matchedActive concatWorld concatActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 44) ((matchedActions.drop 39).take 5) concatWorld concatActive final after := by
  dsimp only
  obtain ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive,
    tailWorld, tailActive, scoreWorld, scoreActive, rootWorld, rootActive, matchedWorld, matchedActive, concatWorld, concatActive,
    cost, nativeCost, entryRun, machine, candidate, queries, wordValue, _, count, _, unbound, events, costEq, _, candidateFresh, wordFresh, prefixes⟩ :=
    entry_pair_left_concat_scope_complete_fresh hw hc view lh lt rh rt table afterHeads output heads tails subtotal total
      leftCell rightCell tableCell leftRead rightRead tableRead input frame covered miss headsTotal tailsTotal
      headSuccess tailSuccess subtotalSuccess rootSuccess
  obtain ⟨final, after, anchor, views, finalMachine, finalQueries, finalCandidate, value77, value78, empty76, root76,
    _, countAfter, _, rootsAfter, _⟩ :=
    pair_left_word_views_complete machine (Helpers.callee 0 0) queries candidate wordValue
      (by rw [count, (CallingCertificate.originalEvaluator_spec).2.1]; decide)
      (by intro slot member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl <;> exact unbound _ (by simp))
  have candidateAfter := views.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by decide +kernel))
    machine.native.valid machine.native.callersValid machine.native.wellFormed candidateFresh
  have wordAfter := views.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by decide +kernel))
    machine.native.valid machine.native.callersValid machine.native.wellFormed wordFresh
  refine ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive,
    tailWorld, tailActive, scoreWorld, scoreActive, rootWorld, rootActive, matchedWorld, matchedActive, concatWorld, concatActive,
    final, after, anchor, cost, nativeCost, entryRun, finalMachine, finalCandidate, finalQueries, finalMachine.value,
    value77, value78, empty76, root76, countAfter.trans count, ?_, events, costEq, candidateAfter, wordAfter, ?_⟩
  · intro slot member
    have outside : slot ∉ [76, 77, 78] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [rootsAfter slot outside]
    exact unbound slot (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      rcases member with rfl | rfl | rfl | rfl | rfl <;> simp)
  · intro fuel budget fuelBound budgetBound
    obtain ⟨common, setup, head, tail, score, root, matched, concat⟩ := prefixes fuel budget fuelBound budgetBound
    exact ⟨common, setup, head, tail, score, root, matched, concat, views.noncall_callee _ (by decide +kernel)⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
