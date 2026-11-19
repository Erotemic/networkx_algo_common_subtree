module

public import SubtreeProofs.Rust.SourcePairRightProvenanceScope
public import SubtreeProofs.Rust.SourcePairRightProvenancePrefixEntry

/-! Parsed entry derives all retained owner bounds through both actual
contraction calls and their complete result cleanup with every earlier prefix. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_right_from_concat_complete_provenance {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    {lh lt rh rt : BalancedWord} {heads tails leftWitness : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (scope : RightConcatScope lh lt rh rt heads tails leftWitness table total active)
    (heldAbove : ∀ slot ∈ [64, 71, 81, 85], LocalOwnersAbove before.memory.length world active slot)
    (count : 96 ≤ active.count) (future : ∀ slot, 88 ≤ slot → active.roots slot = none)
    (childTotal : NativeTotalFresh (.Pair lh lt) (OrderedSolver.appendWord rh rt)) :
    ∃ minimumFuel minimumBudget viewsWorld viewsActive argumentWorld argumentActive callWorld callActive final after result output cost,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      PairRightScope lh lt rh rt heads tails leftWitness total result output final after ∧
      memoized_common_embedding (.Pair lh lt) (OrderedSolver.appendWord rh rt) table = .ok (result, output) ∧
      Derived.scrutinee final after callers (.discriminant (.local 88)) = some (lookupKey result, after) ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, 96 ≤ slot → after.roots slot = none) ∧
      LocalOwnersAbove before.memory.length final after 88 ∧
      (∀ slot ∈ [64, 71, 81, 85], LocalOwnersAbove before.memory.length final after slot) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers (rightCode 22) ((rightActions.drop 15).take 7) world active viewsWorld viewsActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (rightCode 24) ((rightActions.drop 22).take 2) viewsWorld viewsActive argumentWorld argumentActive ∧
        Derived.call (Recursive.original budget fuel) argumentWorld (argumentActive.forgetRefs (rightCode 24)) callers
          .evaluate rightContractionArgs 90 = some (callWorld, callActive, cost) ∧
        Calling.Prefix (Recursive.original budget fuel) callers (rightCode 25) [.call .evaluate rightContractionArgs 90] argumentWorld argumentActive callWorld callActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers rightContractionCases ((rightActions.drop 25).take 11) callWorld callActive final after ∧
        Calling.Prefix (Recursive.original budget fuel) callers rightContractionCases (rightActions.drop 15) world active final after := by
  obtain ⟨viewsWorld, viewsActive, anchor, views, mv, scopeV, leftV, rightV, intermediateV, empty90, root90, _, countV, frameV, rootsV, _⟩ :=
    pair_right_word_views_complete h (Helpers.callee 0 0) scope (by omega)
      (by intro slot member; exact future slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega))
  have heldV : ∀ slot ∈ [64, 71, 81, 85], LocalOwnersAbove before.memory.length viewsWorld viewsActive slot := by
    intro slot member
    exact views.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide +kernel))
      h.native.valid h.native.callersValid h.native.wellFormed (heldAbove slot member)
  obtain ⟨fuel, budget, argumentWorld, argumentActive, callWorld, callActive, final, after, result, output, cost,
    machine, scopeAfter, native, inspection, countAfter, frameAfter, _, _, fresh, heldFinal, stable⟩ :=
    pair_right_scope_complete_provenance mv scopeV leftV rightV intermediateV empty90 root90 heldV (by rw [countV]; exact count)
      (by intro slot member
          rw [rootsV slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; omega)]
          exact future slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega)) childTotal
  obtain ⟨arguments, called, callRun, cleanup, remaining14⟩ := stable fuel budget (by rfl) (by rfl)
  have whole : Calling.Prefix (Recursive.original budget fuel) callers rightContractionCases (rightActions.drop 15) world active final after :=
    Calling.Prefix.append (suffix := rightContractionCases) (rest := (rightActions.drop 22).take 14)
      (views.noncall_callee _ (by decide +kernel)) remaining14
  refine ⟨fuel, budget, viewsWorld, viewsActive, argumentWorld, argumentActive, callWorld, callActive, final, after, result, output, cost,
    machine, scopeAfter, native, inspection, countAfter.trans countV, frameAfter.trans frameV, ?_, fresh, heldFinal, ?_⟩
  · intro slot above
    rw [whole.root_above above (by decide +kernel)]
    exact future slot (by omega)
  · intro largerFuel largerBudget fuelBound budgetBound
    obtain ⟨arguments, called, callRun, cleanup, remaining14⟩ := stable largerFuel largerBudget fuelBound budgetBound
    have viewsRun := views.noncall_callee (Recursive.original largerBudget largerFuel) (by decide +kernel)
    exact ⟨viewsRun, arguments, called, callRun, cleanup,
      Calling.Prefix.append (suffix := rightContractionCases) (rest := (rightActions.drop 22).take 14) viewsRun remaining14⟩


theorem entry_pair_right_scope_complete_provenance {world : World} {callers : List Activation} {previous : Resources}
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
    (leftTotal : NativeTotalFresh (OrderedSolver.appendWord lh lt) (.Pair rh rt))
    (left : CommonEmbedding) (afterLeft : MemoTable)
    (leftSuccess : memoized_common_embedding (OrderedSolver.appendWord lh lt) (.Pair rh rt) afterTails = .ok (some left, afterLeft))
    (rightTotal : NativeTotalFresh (.Pair lh lt) (OrderedSolver.appendWord rh rt)) :
    let packets := inputPackets leftCell rightCell tableCell (.Pair lh lt) (.Pair rh rt) table
    ∃ entered active minimumFuel minimumBudget lookupWorld lookupActive missWorld missActive headWorld headActive tailWorld tailActive scoreWorld scoreActive rootWorld rootActive matchedWorld matchedActive concatWorld concatActive viewsWorld viewsActive argumentWorld argumentActive callWorld callActive leftWorld leftActive rightConcatWorld rightConcatActive rightViewsWorld rightViewsActive rightArgumentWorld rightArgumentActive rightCallWorld rightCallActive final after result output, ∃ cost : Cost, ∃ nativeCost : LookupSource.Cost, ∃ leftCost : Cost, ∃ rightCost : Cost,
      enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount packets = some (entered, active) ∧
      OriginalLoanMachine world callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      PairRightScope lh lt rh rt heads tails left total result output final after ∧
      Derived.scrutinee leftWorld leftActive callers (.discriminant (.local 74)) = some (.variant .optional 1, leftActive) ∧
      memoized_common_embedding (.Pair lh lt) (OrderedSolver.appendWord rh rt) afterLeft = .ok (result, output) ∧
      Derived.scrutinee final after callers (.discriminant (.local 88)) = some (lookupKey result, after) ∧
      after.count = CallingCertificate.originalEvaluator.source.localCount ∧
      (∀ slot, 96 ≤ slot → after.roots slot = none) ∧
      nativeCost.events = MemoSource.concatenateEvents rh rt ∧
      cost = (Cost.local (Action.call .concatenate (concatenateArgs 86 87) 85).weight).plus (SourceEval.Legacy.costMap nativeCost) ∧
      LocalOwnersAbove world.memory.length final after 88 ∧
      (∀ slot ∈ [64, 71, 81, 85], LocalOwnersAbove world.memory.length final after slot) ∧
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
        Calling.Prefix (Recursive.original budget fuel) callers (rightCode 15) (rightActions.take 15) leftWorld leftActive rightConcatWorld rightConcatActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (rightCode 22) ((rightActions.drop 15).take 7) rightConcatWorld rightConcatActive rightViewsWorld rightViewsActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (rightCode 24) ((rightActions.drop 22).take 2) rightViewsWorld rightViewsActive rightArgumentWorld rightArgumentActive ∧
        Derived.call (Recursive.original budget fuel) rightArgumentWorld (rightArgumentActive.forgetRefs (rightCode 24)) callers
          .evaluate rightContractionArgs 90 = some (rightCallWorld, rightCallActive, rightCost) ∧
        Calling.Prefix (Recursive.original budget fuel) callers (rightCode 25) [.call .evaluate rightContractionArgs 90] rightArgumentWorld rightArgumentActive rightCallWorld rightCallActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers rightContractionCases ((rightActions.drop 25).take 11) rightCallWorld rightCallActive final after ∧
        Calling.Prefix (Recursive.original budget fuel) callers rightContractionCases rightActions leftWorld leftActive final after := by
  dsimp only
  obtain ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive,
    tailWorld, tailActive, scoreWorld, scoreActive, rootWorld, rootActive, matchedWorld, matchedActive, concatWorld, concatActive,
    viewsWorld, viewsActive, argumentWorld, argumentActive, callWorld, callActive, leftWorld, leftActive, rightConcatWorld, rightConcatActive,
    cost, nativeCost, leftCost, entryRun, machine, scopeC, leftInspection, countC, futureC, events, costEq, heldC, prefixes⟩ :=
    entry_pair_right_prefix_complete_provenance hw hc view lh lt rh rt table afterHeads afterTails heads tails subtotal total
      leftCell rightCell tableCell leftRead rightRead tableRead input frame covered miss headsTotal tailsTotal
      headSuccess tailSuccess subtotalSuccess rootSuccess leftTotal left afterLeft leftSuccess
  obtain ⟨rightFuel, rightBudget, rightViewsWorld, rightViewsActive, rightArgumentWorld, rightArgumentActive, rightCallWorld, rightCallActive,
    final, after, result, output, rightCost, finalMachine, scope, native, inspection, countAfter, _, futureAfter, fresh, heldFinal, stable⟩ :=
    pair_right_from_concat_complete_provenance machine scopeC heldC
      (by rw [countC, (CallingCertificate.originalEvaluator_spec).2.1]; decide) futureC rightTotal
  let jointFuel := max minFuel rightFuel
  let jointBudget := max minBudget rightBudget
  refine ⟨entered, active, jointFuel, jointBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive,
    tailWorld, tailActive, scoreWorld, scoreActive, rootWorld, rootActive, matchedWorld, matchedActive, concatWorld, concatActive,
    viewsWorld, viewsActive, argumentWorld, argumentActive, callWorld, callActive, leftWorld, leftActive, rightConcatWorld, rightConcatActive,
    rightViewsWorld, rightViewsActive, rightArgumentWorld, rightArgumentActive, rightCallWorld, rightCallActive, final, after, result, output,
    cost, nativeCost, leftCost, rightCost, entryRun, finalMachine, scope, leftInspection, native, inspection,
    countAfter.trans countC, futureAfter, events, costEq, fresh, heldFinal, ?_⟩
  intro fuel budget fuelBound budgetBound
  obtain ⟨common, setup, head, tail, score, root, matched, concat, views, arguments, called, callRun, cleanup, leftWhole, right15⟩ :=
    prefixes fuel budget ((Nat.le_max_left _ _).trans fuelBound) ((Nat.le_max_left _ _).trans budgetBound)
  obtain ⟨rightViews, rightArguments, rightCalled, rightCallRun, rightCleanup, right21⟩ :=
    stable fuel budget ((Nat.le_max_right _ _).trans fuelBound) ((Nat.le_max_right _ _).trans budgetBound)
  have rightWhole : Calling.Prefix (Recursive.original budget fuel) callers rightContractionCases rightActions leftWorld leftActive final after :=
    Calling.Prefix.append (suffix := rightContractionCases) (rest := rightActions.drop 15) right15 right21
  exact ⟨common, setup, head, tail, score, root, matched, concat, views, arguments, called, callRun, cleanup, leftWhole, right15,
    rightViews, rightArguments, rightCalled, rightCallRun, rightCleanup, rightWhole⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
