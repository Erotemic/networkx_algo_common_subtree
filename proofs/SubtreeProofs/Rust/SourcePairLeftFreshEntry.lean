module

public import SubtreeProofs.Rust.SourcePairLeftFreshScope
public import SubtreeProofs.Rust.SourcePairLeftWordViewsFreshEntry
public import SubtreeProofs.Rust.SourcePrefixRootBounds

/-! Parsed evaluator entry reaches the complete left contraction result scope
and its actual optional switch, with all future parent locals still unbound. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem entry_pair_left_scope_complete_fresh {world : World} {callers : List Activation} {previous : Resources}
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
    (headsTotal : NativeTotalFresh lh rh) (tailsTotal : NativeTotalFresh lt rt)
    (headSuccess : memoized_common_embedding lh rh table = .ok (some heads, afterHeads))
    (tailSuccess : memoized_common_embedding lt rt afterHeads = .ok (some tails, afterTails))
    (subtotalSuccess : Aeneas.Std.U32.checked_add heads.edges tails.edges = some subtotal)
    (rootSuccess : Aeneas.Std.U32.checked_add subtotal 1#u32 = some total)
    (leftTotal : NativeTotalFresh (OrderedSolver.appendWord lh lt) (.Pair rh rt)) :
    let packets := inputPackets leftCell rightCell tableCell (.Pair lh lt) (.Pair rh rt) table
    ∃ entered active minimumFuel minimumBudget lookupWorld lookupActive missWorld missActive headWorld headActive tailWorld tailActive scoreWorld scoreActive rootWorld rootActive matchedWorld matchedActive concatWorld concatActive viewsWorld viewsActive argumentWorld argumentActive callWorld callActive final after result output cost,
      enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount packets = some (entered, active) ∧
      OriginalLoanMachine world callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      PairLeftScope lh lt rh rt heads tails total result output final after ∧
      memoized_common_embedding (OrderedSolver.appendWord lh lt) (.Pair rh rt) afterTails = .ok (result, output) ∧
      Derived.scrutinee final after callers (.discriminant (.local 74)) = some (lookupKey result, after) ∧
      after.count = CallingCertificate.originalEvaluator.source.localCount ∧
      (∀ slot, 82 ≤ slot → after.roots slot = none) ∧
      LocalOwnersAbove world.memory.length final after 74 ∧
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
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 44) ((matchedActions.drop 39).take 5) concatWorld concatActive viewsWorld viewsActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 48) ((matchedActions.drop 44).take 4) viewsWorld viewsActive argumentWorld argumentActive ∧
        Derived.call (Recursive.original budget fuel) argumentWorld (argumentActive.forgetRefs (matchedCode 48)) callers
          .evaluate leftContractionArgs 76 = some (callWorld, callActive, cost) ∧
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 49) [.call .evaluate leftContractionArgs 76] argumentWorld argumentActive callWorld callActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers matchedCases ((matchedActions.drop 49).take 11) callWorld callActive final after ∧
        Calling.Prefix (Recursive.original budget fuel) callers matchedCases matchedActions rootWorld rootActive final after := by
  dsimp only
  obtain ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive,
    tailWorld, tailActive, scoreWorld, scoreActive, rootWorld, rootActive, matchedWorld, matchedActive, concatWorld, concatActive,
    viewsWorld, viewsActive, anchor, _, _, entryRun, machine, candidate, queries, _, left, view78, empty76, root76,
    count, unbound, _, _, candidateFresh, wordFresh, prefixes⟩ :=
    entry_pair_left_word_views_complete_fresh hw hc view lh lt rh rt table afterHeads afterTails heads tails subtotal total
      leftCell rightCell tableCell leftRead rightRead tableRead input frame covered miss headsTotal tailsTotal
      headSuccess tailSuccess subtotalSuccess rootSuccess
  obtain ⟨leftFuel, leftBudget, argumentWorld, argumentActive, callWorld, callActive, final, after, result, output, cost,
    finalMachine, scope, native, inspection, countAfter, _, _, _, resultFinal, candidateFinal, wordFinal, stable⟩ :=
    pair_left_scope_complete_fresh machine queries candidate left view78 empty76 root76 candidateFresh wordFresh
      (by rw [count, (CallingCertificate.originalEvaluator_spec).2.1]; decide) unbound leftTotal
  let jointFuel := max minFuel leftFuel
  let jointBudget := max minBudget leftBudget
  obtain ⟨common, setup, head, tail, score, root, matched, concat, views⟩ :=
    prefixes jointFuel jointBudget (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  obtain ⟨arguments, callRun, called, cleanup, _⟩ := stable jointFuel jointBudget (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  obtain ⟨sameWorld, sameActive, sameEntry, _, _, _, initiallyUnbound, _⟩ :=
    native_entry_machine hw hc view (.Pair lh lt) (.Pair rh rt) table leftCell rightCell tableCell leftRead rightRead tableRead input frame covered
  have same := Prod.mk.inj (Option.some.inj (entryRun.symm.trans sameEntry))
  obtain ⟨rfl, rfl⟩ := same
  have future : ∀ slot, 82 ≤ slot → after.roots slot = none := by
    intro slot above
    rw [cleanup.root_above above (by decide +kernel), called.root_above above (by decide +kernel),
      arguments.root_above above (by decide +kernel), views.root_above above (by decide +kernel),
      concat.root_above above (by decide +kernel), matched.root_above above (by decide +kernel),
      root.root_above above (by decide +kernel), score.root_above above (by decide +kernel),
      tail.root_above above (by decide +kernel), head.root_above above (by decide +kernel),
      setup.root_above above (by decide +kernel), common.root_above above (by decide +kernel)]
    exact initiallyUnbound slot (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      omega)
  refine ⟨entered, active, jointFuel, jointBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive,
    tailWorld, tailActive, scoreWorld, scoreActive, rootWorld, rootActive, matchedWorld, matchedActive, concatWorld, concatActive,
    viewsWorld, viewsActive, argumentWorld, argumentActive, callWorld, callActive, final, after, result, output, cost,
    entryRun, finalMachine, scope, native, inspection, countAfter.trans count, future, resultFinal, candidateFinal, wordFinal, ?_⟩
  intro fuel budget fuelBound budgetBound
  obtain ⟨common, setup, head, tail, score, root, matched, concat, views⟩ :=
    prefixes fuel budget ((Nat.le_max_left _ _).trans fuelBound) ((Nat.le_max_left _ _).trans budgetBound)
  obtain ⟨arguments, callRun, called, cleanup, remaining16⟩ :=
    stable fuel budget ((Nat.le_max_right _ _).trans fuelBound) ((Nat.le_max_right _ _).trans budgetBound)
  have last21 : Calling.Prefix (Recursive.original budget fuel) callers matchedCases ((matchedActions.drop 39).take 21)
      concatWorld concatActive final after :=
    Calling.Prefix.append (suffix := matchedCases) (rest := (matchedActions.drop 44).take 16) views remaining16
  have last30 : Calling.Prefix (Recursive.original budget fuel) callers matchedCases ((matchedActions.drop 30).take 30)
      matchedWorld matchedActive final after :=
    Calling.Prefix.append (suffix := matchedCases) (rest := (matchedActions.drop 39).take 21) concat last21
  have whole : Calling.Prefix (Recursive.original budget fuel) callers matchedCases matchedActions rootWorld rootActive final after :=
    Calling.Prefix.append (suffix := matchedCases) (rest := (matchedActions.drop 30).take 30) matched last30
  exact ⟨common, setup, head, tail, score, root, matched, concat, views, arguments, callRun, called, cleanup, whole⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
