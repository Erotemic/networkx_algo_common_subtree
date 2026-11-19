module

public import SubtreeProofs.Rust.SourcePairRightPrefix

/-! Parsed evaluator entry constructs the successful left payload and owned
right contraction query through thirteen stable actual source boundaries. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem entry_pair_right_prefix_complete {world : World} {callers : List Activation} {previous : Resources}
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
    (leftTotal : NativeTotal (OrderedSolver.appendWord lh lt) (.Pair rh rt))
    (left : CommonEmbedding) (afterLeft : MemoTable)
    (leftSuccess : memoized_common_embedding (OrderedSolver.appendWord lh lt) (.Pair rh rt) afterTails = .ok (some left, afterLeft)) :
    let packets := inputPackets leftCell rightCell tableCell (.Pair lh lt) (.Pair rh rt) table
    ∃ entered active minimumFuel minimumBudget lookupWorld lookupActive missWorld missActive headWorld headActive tailWorld tailActive scoreWorld scoreActive rootWorld rootActive matchedWorld matchedActive concatWorld concatActive viewsWorld viewsActive argumentWorld argumentActive callWorld callActive leftWorld leftActive final after, ∃ cost : Cost, ∃ nativeCost : LookupSource.Cost, ∃ leftCost : Cost,
      enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount packets = some (entered, active) ∧
      OriginalLoanMachine world callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      RightConcatScope lh lt rh rt heads tails left afterLeft total after ∧
      Derived.scrutinee leftWorld leftActive callers (.discriminant (.local 74)) = some (.variant .optional 1, leftActive) ∧
      after.count = CallingCertificate.originalEvaluator.source.localCount ∧
      (∀ slot, 88 ≤ slot → after.roots slot = none) ∧
      nativeCost.events = MemoSource.concatenateEvents rh rt ∧
      cost = (Cost.local (Action.call .concatenate (concatenateArgs 86 87) 85).weight).plus (SourceEval.Legacy.costMap nativeCost) ∧
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
          .evaluate leftContractionArgs 76 = some (callWorld, callActive, leftCost) ∧
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 49) [.call .evaluate leftContractionArgs 76] argumentWorld argumentActive callWorld callActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers matchedCases ((matchedActions.drop 49).take 11) callWorld callActive leftWorld leftActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers matchedCases matchedActions rootWorld rootActive leftWorld leftActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (rightCode 15) (rightActions.take 15) leftWorld leftActive final after := by
  dsimp only
  obtain ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive,
    tailWorld, tailActive, scoreWorld, scoreActive, rootWorld, rootActive, matchedWorld, matchedActive, concatWorld, concatActive,
    viewsWorld, viewsActive, argumentWorld, argumentActive, callWorld, callActive, leftWorld, leftActive, result, output, leftCost,
    entryRun, machine, leftScope, native, inspection, count, future, prefixes⟩ :=
    entry_pair_left_scope_complete hw hc view lh lt rh rt table afterHeads afterTails heads tails subtotal total
      leftCell rightCell tableCell leftRead rightRead tableRead input frame covered miss headsTotal tailsTotal
      headSuccess tailSuccess subtotalSuccess rootSuccess leftTotal
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (native.symm.trans leftSuccess))
  obtain ⟨rightFuel, rightBudget, final, after, cost, nativeCost, finalMachine, scope, countAfter, _, _, events, costEq, _, stable⟩ :=
    pair_right_prefix_complete machine leftScope
      (by rw [count, (CallingCertificate.originalEvaluator_spec).2.1]; decide)
      (by intro slot member; exact future slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega))
  let jointFuel := max minFuel rightFuel
  let jointBudget := max minBudget rightBudget
  have rightRun := stable jointFuel jointBudget (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have futureAfter : ∀ slot, 88 ≤ slot → after.roots slot = none := by
    intro slot above
    rw [rightRun.root_above above (by decide +kernel)]
    exact future slot (by omega)
  refine ⟨entered, active, jointFuel, jointBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive,
    tailWorld, tailActive, scoreWorld, scoreActive, rootWorld, rootActive, matchedWorld, matchedActive, concatWorld, concatActive,
    viewsWorld, viewsActive, argumentWorld, argumentActive, callWorld, callActive, leftWorld, leftActive, final, after,
    cost, nativeCost, leftCost, entryRun, finalMachine, scope, inspection, countAfter.trans count, futureAfter, events, costEq, ?_⟩
  intro fuel budget fuelBound budgetBound
  obtain ⟨common, setup, head, tail, score, root, matched, concat, views, arguments, called, callRun, cleanup, whole⟩ :=
    prefixes fuel budget ((Nat.le_max_left _ _).trans fuelBound) ((Nat.le_max_left _ _).trans budgetBound)
  exact ⟨common, setup, head, tail, score, root, matched, concat, views, arguments, called, callRun, cleanup, whole,
    stable fuel budget ((Nat.le_max_right _ _).trans fuelBound) ((Nat.le_max_right _ _).trans budgetBound)⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
