module

public import SubtreeProofs.Rust.SourcePairReturnStorage

/-! Augment the existing parsed native right-result endpoint with derived empty
return storage and checked local typing. Every earlier hypothesis, checkpoint,
resource/provenance guarantee and stable bound remains exposed. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem entry_pair_right_scope_storage_complete_provenance {world : World} {callers : List Activation} {previous : Resources}
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
      EmptyRootStorage final after 0 ∧ LocalsTyped CallingCertificate.originalEvaluator.locals after.state ∧
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
    rightViewsWorld, rightViewsActive, rightArgumentWorld, rightArgumentActive, rightCallWorld, rightCallActive, final, after, result, output,
    cost, nativeCost, leftCost, rightCost, entryRun, machine, scope, leftInspection, native, inspection, count, future, events, costEq,
    fresh, held, stable⟩ := entry_pair_right_scope_complete_provenance hw hc view lh lt rh rt table afterHeads afterTails heads tails subtotal total
      leftCell rightCell tableCell leftRead rightRead tableRead input frame covered miss headsTotal tailsTotal headSuccess tailSuccess
      subtotalSuccess rootSuccess leftTotal left afterLeft leftSuccess rightTotal
  obtain ⟨sameWorld, sameActive, sameEntry, initialMachine, state, _, _, _⟩ :=
    native_entry_machine hw hc view (.Pair lh lt) (.Pair rh rt) table leftCell rightCell tableCell leftRead rightRead tableRead input frame covered
  have same := Prod.mk.inj (Option.some.inj (entryRun.symm.trans sameEntry))
  obtain ⟨rfl, rfl⟩ := same
  have inputTypes : SnapshotFieldsTyped [.reference (encodeWord (.Pair lh lt)), .reference (encodeWord (.Pair rh rt)), encodeTable table]
      (Types.inputs CallingCertificate.originalEvaluator.source.function) := by
    rw [CallingCertificate.originalEvaluator_spec.1]
    exact .cons (.shared (word_typed _)) (.cons (.shared (word_typed _)) (.cons (table_typed _) .nil))
  have locals : LocalsTyped CallingCertificate.originalEvaluator.locals active.state := by
    rw [state]
    exact Types.initial_typed inputTypes CallingCertificate.originalEvaluator.boundary
  obtain ⟨common, setup, head, tail, score, root, _, _, _, _, _, _, _, leftWhole, _, _, _, _, _, _, rightWhole⟩ :=
    stable minFuel minBudget (by rfl) (by rfl)
  have context := pair_right_return_storage minFuel minBudget initialMachine.valid initialMachine.callersValid initialMachine.wellFormed locals
    common setup head tail score root leftWhole rightWhole
  exact ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive,
    tailWorld, tailActive, scoreWorld, scoreActive, rootWorld, rootActive, matchedWorld, matchedActive, concatWorld, concatActive,
    viewsWorld, viewsActive, argumentWorld, argumentActive, callWorld, callActive, leftWorld, leftActive, rightConcatWorld, rightConcatActive,
    rightViewsWorld, rightViewsActive, rightArgumentWorld, rightArgumentActive, rightCallWorld, rightCallActive, final, after, result, output,
    cost, nativeCost, leftCost, rightCost, entryRun, machine, scope, leftInspection, native, inspection, count, future, events, costEq,
    fresh, held, context.storage, context.typed, stable⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
