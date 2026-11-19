module

public import SubtreeProofs.Rust.SourceRootOverflowContinuation
public import SubtreeProofs.Rust.SourcePairNextRouting
public import SubtreeProofs.Rust.SourceEvaluatorPrefixConstraints
public import SubtreeProofs.Rust.SourceOptionalPayloadTag
public import SubtreeProofs.Rust.SourceEvaluatorRouteTypes

/-! Construct the whole original pair/pair body when both recursive children
succeed but their root score overflows. No parent execution is assumed. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem entry_root_overflow_body_complete {world : World} {callers : List Activation} {previous : Resources}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (lh lt rh rt : BalancedWord) (table afterHeads output : MemoTable) (heads tails : CommonEmbedding)
    (subtotal : Aeneas.Std.U32) (leftCell rightCell tableCell : Cell)
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
    (overflow : Aeneas.Std.U32.checked_add subtotal 1#u32 = none) :
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
    tailWorld, tailActive, scoreWorld, scoreActive, rootWorld, rootActive, entryRun, machine, rootScope, _, rootInspection,
    headsFresh, tailsFresh, stable⟩ :=
    entry_pair_root_score_scope_complete_fresh hw hc view lh lt rh rt table afterHeads output heads tails subtotal leftCell rightCell tableCell
      leftRead rightRead tableRead input frame covered miss headsTotal tailsTotal headSuccess tailSuccess subtotalSuccess
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
  obtain ⟨common, setup, head, tail, score, root⟩ := stable fuel budget (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  obtain ⟨earlyCommon, earlySetup⟩ := earlyStable fuel budget (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  obtain ⟨rfl, rfl⟩ := common.unique earlyCommon
  obtain ⟨rfl, rfl⟩ := setup.unique earlySetup
  have respects := Recursive.original_typed_respects budget fuel
  have sourceTyped := Types.original_run_typed fuel
  have constraints := evaluator_prefix_constraints
  have c0 := common.typed_spec respects sourceTyped initialMachine.valid initialMachine.callersValid initialMachine.wellFormed typed constraints.common
  have c1 := setup.typed_spec respects sourceTyped c0.1 c0.2.1 c0.2.2.1 c0.2.2.2 constraints.miss
  have c2 := head.typed_spec respects sourceTyped c1.1 c1.2.1 c1.2.2.1 c1.2.2.2 constraints.heads
  have c3 := tail.typed_spec respects sourceTyped c2.1 c2.2.1 c2.2.2.1 c2.2.2.2 constraints.tails
  have c4 := score.typed_spec respects sourceTyped c3.1 c3.2.1 c3.2.2.1 c3.2.2.2 constraints.scores
  have presentTail := pair_tail_root_presence entryRun (by simp [inputPackets]) common setup head tail
  have presentScore := pair_score_root_presence presentTail score
  have present := pair_root_score_root_presence presentScore root
  have count : 113 ≤ rootActive.count := by
    rw [root.shape.2.1, score.shape.2.1, tail.shape.2.1, head.shape.2.1, setup.shape.2.1, common.shape.2.1, initialCount]
  have context := pair_root_return_storage fuel budget initialMachine.valid initialMachine.callersValid initialMachine.wellFormed typed
    common setup head tail score root
  have older := pair_root_older_masks fuel budget initialMachine.valid initialMachine.callersValid initialMachine.wellFormed typed
    common setup head tail score root
  have nativeOverflow : checkedAdd32 subtotal.val 1 = none := by
    change checkedAdd32 subtotal.val (1#u32).val = none
    rw [checkedAdd32_native, overflow]; rfl
  obtain ⟨rootJoinWorld, rootJoinActive, rootJoinCost, tailJoinWorld, tailJoinActive, tailJoinCost,
    headJoinWorld, headJoinActive, headJoinCost, joinWorld, joinActive, joinCost,
    final, after, cell, returnCost, rootRun, cleanupTailsRun, cleanupHeadsRun, cleanupInputsRun,
    returned, empty, separate, fresh, kept⟩ :=
    root_overflow_continuation_complete machine (Recursive.original budget fuel) rootScope context.storage present count
      older headsFresh tailsFresh nativeOverflow rootInspection
  have headInspection := Calling.Prefix.typed_payload_tag respects sourceTyped
    (before := tailActions.take 1) (rest := tailActions.drop 2) (slot := 31) (destination := 38)
    tail c2.1 c2.2.1 c2.2.2.1 c2.2.2.2
    (fun act member => constraints.tails act (List.mem_of_mem_take member)) evaluator_cleanup_optional_types.1
    (Or.inl rfl) (.adt .optional) (by decide +kernel)
    (by intro state value remaining run; simp only [SourceEval.operand] at run; exact (Partial.Locals.move_spec run).1)
  have tailInspection := Calling.Prefix.typed_payload_tag respects sourceTyped
    (before := scoreActions.take 1) (rest := scoreActions.drop 2) (slot := 41) (destination := 48)
    score c3.1 c3.2.1 c3.2.2.1 c3.2.2.2
    (fun act member => constraints.scores act (List.mem_of_mem_take member)) evaluator_cleanup_optional_types.2
    (Or.inl rfl) (.adt .optional) (by decide +kernel)
    (by intro state value remaining run; simp only [SourceEval.operand] at run; exact (Partial.Locals.move_spec run).1)
  have subtotalInspection := Calling.Prefix.typed_payload_tag respects sourceTyped
    (before := rootScoreActions.take 1) (rest := rootScoreActions.drop 2) (slot := 52) (destination := 55)
    root c4.1 c4.2.1 c4.2.2.1 c4.2.2.2
    (fun act member => constraints.roots act (List.mem_of_mem_take member)) evaluator_score_option_types.1
    (Or.inr ⟨.u32, rfl⟩) (.option .u32) (by decide +kernel)
    (by intro state value remaining run; exact (copy_nonowning run).2.1)
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
