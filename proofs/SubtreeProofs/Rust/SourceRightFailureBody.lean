module

public import SubtreeProofs.Rust.SourceRightFailureContinuation
public import SubtreeProofs.Rust.SourcePairNextRouting
public import SubtreeProofs.Rust.SourceEvaluatorPrefixConstraints
public import SubtreeProofs.Rust.SourceOptionalPayloadTag
public import SubtreeProofs.Rust.SourcePairRouteInspections

/-! Construct the whole original pair/pair body when left contraction succeeds
and right contraction returns None, including every cleanup join. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem entry_right_failure_body_complete {world : World} {callers : List Activation} {previous : Resources}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (lh lt rh rt : BalancedWord) (table afterHeads afterTails output : MemoTable) (heads tails : CommonEmbedding)
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
    (leftWitness : CommonEmbedding) (afterLeft : MemoTable)
    (leftSuccess : memoized_common_embedding (OrderedSolver.appendWord lh lt) (.Pair rh rt) afterTails = .ok (some leftWitness, afterLeft))
    (rightTotal : NativeTotalFresh (.Pair lh lt) (OrderedSolver.appendWord rh rt))
    (rightFailure : memoized_common_embedding (.Pair lh lt) (OrderedSolver.appendWord rh rt) afterLeft = .ok (none, output)) :
    ∃ entered active fuel budget final after cell cost,
      enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount
        (inputPackets leftCell rightCell tableCell (.Pair lh lt) (.Pair rh rt) table) = some (entered, active) ∧
      LoanSafeMachine world callers previous external entered active ∧
      active.state = initialState [.reference (encodeWord (.Pair lh lt)), .reference (encodeWord (.Pair rh rt)), encodeTable table] ∧
      Calling.exec (Recursive.original budget fuel) callers body entered active =
        some (.returned final after (cell, encodeOutput none output), cost) ∧
      (∀ slot, after.state slot = .empty) ∧ after.RootsSeparate callers ∧
      (∀ slot binding, after.roots slot = some binding → world.memory.length ≤ binding.address) ∧
      Preserves world final previous.reads := by
  obtain ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive,
    tailWorld, tailActive, scoreWorld, scoreActive, rootWorld, rootActive, matchedWorld, matchedActive, concatWorld, concatActive,
    viewsWorld, viewsActive, argumentWorld, argumentActive, callWorld, callActive, leftWorld, leftActive, rightConcatWorld, rightConcatActive,
    rightViewsWorld, rightViewsActive, rightArgumentWorld, rightArgumentActive, rightCallWorld, rightCallActive, rightWorld, rightActive,
    result, foundTable, _, _, _, _, entryRun, machine, scope, leftInspection, native, _, count, _, _, _, _, held, storage, _, stable⟩ :=
    entry_pair_right_scope_storage_complete_provenance hw hc view lh lt rh rt table afterHeads afterTails heads tails subtotal total
      leftCell rightCell tableCell leftRead rightRead tableRead input frame covered miss headsTotal tailsTotal headSuccess tailSuccess
      subtotalSuccess rootSuccess leftTotal leftWitness afterLeft leftSuccess rightTotal
  have nativeFields := Prod.mk.inj (Aeneas.Std.Result.ok_injective (native.symm.trans rightFailure))
  have resultEq : result = none := nativeFields.1
  have tableEq : foundTable = output := nativeFields.2
  subst result
  subst foundTable
  obtain ⟨sameWorld, sameActive, sameEntry, initialMachine, state, initialCount, _, _⟩ :=
    native_entry_machine hw hc view (.Pair lh lt) (.Pair rh rt) table leftCell rightCell tableCell
      leftRead rightRead tableRead input frame covered
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (entryRun.symm.trans sameEntry))
  have inputTypes : SnapshotFieldsTyped [.reference (encodeWord (.Pair lh lt)), .reference (encodeWord (.Pair rh rt)), encodeTable table]
      (Types.inputs CallingCertificate.originalEvaluator.source.function) := by
    rw [CallingCertificate.originalEvaluator_spec.1]
    exact .cons (.shared (word_typed _)) (.cons (.shared (word_typed _)) (.cons (table_typed _) .nil))
  have typed : LocalsTyped CallingCertificate.originalEvaluator.locals active.state := by
    rw [state]
    exact Types.initial_typed inputTypes CallingCertificate.originalEvaluator.boundary
  obtain ⟨earlyEntered, earlyActive, earlyFuel, earlyBudget, lookupWorld2, lookupActive2, missWorld2, missActive2, earlyEntry, _,
    missMachine, missScope, _, _, _, _, lookupInspection, _, _, earlyStable⟩ :=
    entry_miss_setup_complete hw hc view (.Pair lh lt) (.Pair rh rt) table leftCell rightCell tableCell
      leftRead rightRead tableRead input frame covered miss
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (entryRun.symm.trans earlyEntry))
  let fuel := max minFuel earlyFuel
  let budget := max minBudget earlyBudget
  obtain ⟨common, setup, head, tail, score, root, _, _, _, _, _, _, _, left, _, _, _, _, _, _, right⟩ := stable fuel budget (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  obtain ⟨earlyCommon, earlySetup⟩ := earlyStable fuel budget (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  obtain ⟨rfl, rfl⟩ := common.unique earlyCommon
  obtain ⟨rfl, rfl⟩ := setup.unique earlySetup
  have older := pair_right_older_masks fuel budget initialMachine.valid initialMachine.callersValid initialMachine.wellFormed typed
    common setup head tail score root left right
  have present := pair_right_root_presence fuel budget entryRun (by simp [inputPackets]) common setup head tail score root left right
  obtain ⟨rightJoinWorld, rightJoinActive, rightJoinCost, leftJoinWorld, leftJoinActive, leftJoinCost,
    rootJoinWorld, rootJoinActive, rootJoinCost, tailJoinWorld, tailJoinActive, tailJoinCost,
    headJoinWorld, headJoinActive, headJoinCost, joinWorld, joinActive, joinCost,
    final, after, cell, returnCost, rightRun, cleanupLeftRun, cleanupSubtotalRun, cleanupTailsRun, cleanupHeadsRun, cleanupInputsRun,
    returned, empty, separate, fresh, kept⟩ :=
    right_failure_continuation_complete machine (Recursive.original budget fuel) scope storage older present
      (by rw [count, CallingCertificate.originalEvaluator_spec.2.1]) held
  obtain ⟨headInspection, tailInspection, subtotalInspection, rootInspection⟩ :=
    pair_successful_route_inspections fuel budget initialMachine.valid initialMachine.callersValid initialMachine.wellFormed typed
      common setup head tail score root left
  obtain ⟨rightCost, contractRightRun⟩ := right.exec rightRun
  have contractRightWhole : Calling.exec (Recursive.original budget fuel) callers contractRight leftWorld leftActive =
      some (.next rightJoinWorld rightJoinActive, rightCost) := by rw [contractRight_actions]; exact contractRightRun
  have leftRun : Calling.exec (Recursive.original budget fuel) callers matchedCases leftWorld leftActive =
      some (.next leftJoinWorld leftJoinActive,
        ((Cost.local (1 + (Scrutinee.discriminant (.local 74)).weight)).plus rightCost).plus leftJoinCost) := by
    rw [matchedCases, Calling.exec_switch, leftInspection]
    simp [Control.selectSource, Control.selectIndex, contractRightWhole, cleanupLeftRun]
  obtain ⟨leftCost, contractLeftRun⟩ := left.exec leftRun
  have contractLeftWhole : Calling.exec (Recursive.original budget fuel) callers contractLeft rootWorld rootActive =
      some (.next leftJoinWorld leftJoinActive, leftCost) := by rw [contractLeft_actions]; exact contractLeftRun
  have rootRun : Calling.exec (Recursive.original budget fuel) callers rootScoreCases rootWorld rootActive =
      some (.next rootJoinWorld rootJoinActive,
        ((Cost.local (1 + (Scrutinee.discriminant (.local 59)).weight)).plus leftCost).plus rootJoinCost) := by
    rw [rootScoreCases, Calling.exec_switch, rootInspection]
    simp [Control.selectSource, Control.selectIndex, contractLeftWhole, cleanupSubtotalRun]
  obtain ⟨rootCost, addRootRun⟩ := root.exec rootRun
  have addRootWhole : Calling.exec (Recursive.original budget fuel) callers addRoot scoreWorld scoreActive =
      some (.next rootJoinWorld rootJoinActive, rootCost) := by rw [addRoot_actions]; exact addRootRun
  have scoreRun : Calling.exec (Recursive.original budget fuel) callers scoreCases scoreWorld scoreActive =
      some (.next tailJoinWorld tailJoinActive,
        ((Cost.local (1 + (Scrutinee.discriminant (.local 52)).weight)).plus rootCost).plus tailJoinCost) := by
    rw [scoreCases, Calling.exec_switch, subtotalInspection]
    simp [Control.selectSource, Control.selectIndex, addRootWhole, cleanupTailsRun]
  obtain ⟨scoreCost, addScoresRun⟩ := score.exec scoreRun
  have addScoresWhole : Calling.exec (Recursive.original budget fuel) callers addScores tailWorld tailActive =
      some (.next tailJoinWorld tailJoinActive, scoreCost) := by rw [addScores_actions]; exact addScoresRun
  have tailCasesRun : Calling.exec (Recursive.original budget fuel) callers tailCases tailWorld tailActive =
      some (.next headJoinWorld headJoinActive,
        ((Cost.local (1 + (Scrutinee.discriminant (.local 41)).weight)).plus scoreCost).plus headJoinCost) := by
    rw [tailCases, Calling.exec_switch, tailInspection]
    simp [Control.selectSource, Control.selectIndex, addScoresWhole, cleanupHeadsRun]
  obtain ⟨tailCost, tailRun⟩ := tail.exec tailCasesRun
  have recurseTailsRun : Calling.exec (Recursive.original budget fuel) callers recurseTails headWorld headActive =
      some (.next headJoinWorld headJoinActive, tailCost) := by rw [recurseTails_actions]; exact tailRun
  have headCasesRun : Calling.exec (Recursive.original budget fuel) callers headCases headWorld headActive =
      some (.next joinWorld joinActive,
        ((Cost.local (1 + (Scrutinee.discriminant (.local 31)).weight)).plus tailCost).plus joinCost) := by
    rw [headCases, Calling.exec_switch, headInspection]
    simp [Control.selectSource, Control.selectIndex, recurseTailsRun, cleanupInputsRun]
  obtain ⟨headCost, headRun⟩ := head.exec headCasesRun
  have recurseHeadsRun : Calling.exec (Recursive.original budget fuel) callers recurseHeads missWorld missActive =
      some (.next joinWorld joinActive, headCost) := by rw [recurseHeads_actions]; exact headRun
  obtain ⟨casesCost, casesRun⟩ := pair_cases_next missMachine (Recursive.original budget fuel) missScope recurseHeadsRun
  obtain ⟨missCost, missRun⟩ := setup.exec casesRun
  have cacheMissRun : Calling.exec (Recursive.original budget fuel) callers cacheMiss lookupWorld lookupActive =
      some (.next joinWorld joinActive, missCost) := by rw [cacheMiss_actions]; exact missRun
  have lookupRun : Calling.exec (Recursive.original budget fuel) callers lookupSwitch lookupWorld lookupActive =
      some (.returned final after (cell, encodeOutput none output),
        ((Cost.local (1 + (Scrutinee.discriminant (.local 4)).weight)).plus missCost).plus returnCost) := by
    rw [lookupSwitch, Calling.exec_switch, lookupInspection]
    simp [Control.selectSource, Control.selectIndex, cacheMissRun, returned]
  obtain ⟨cost, whole⟩ := common.exec lookupRun
  refine ⟨entered, active, fuel, budget, final, after, cell, cost, entryRun, initialMachine, state, ?_, empty, separate, fresh, kept⟩
  rw [← actual_body, actual_body_common_prefix]
  exact whole

end SubtreeProofs.Rust.SourceEval.Evaluator
