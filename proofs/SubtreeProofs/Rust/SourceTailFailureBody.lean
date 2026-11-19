module

public import SubtreeProofs.Rust.SourceTailFailureContinuation
public import SubtreeProofs.Rust.SourcePairHeadTailFreshEntry
public import SubtreeProofs.Rust.SourcePairNextRouting
public import SubtreeProofs.Rust.SourceEvaluatorPrefixConstraints

/-! Construct the whole original parent body when the head succeeds and the
smaller tail request returns None, including both actual cleanup joins. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem entry_tail_failure_body_complete {world : World} {callers : List Activation} {previous : Resources}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (lh lt rh rt : BalancedWord) (table afterHeads output : MemoTable) (heads : CommonEmbedding)
    (leftCell rightCell tableCell : Cell)
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
    (tailFailure : memoized_common_embedding lt rt afterHeads = .ok (none, output)) :
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
    tailWorld, tailActive, result, foundTable, entryRun, headScope, machine, tailScope, tailInspection, native, headsFresh, _, stable⟩ :=
    entry_pair_tail_scope_complete_fresh hw hc view lh lt rh rt table afterHeads heads leftCell rightCell tableCell
      leftRead rightRead tableRead input frame covered miss headsTotal tailsTotal headSuccess
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (native.symm.trans tailFailure))
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
  obtain ⟨common, setup, head, tail⟩ := stable fuel budget (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  obtain ⟨earlyCommon, earlySetup⟩ := earlyStable fuel budget (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  obtain ⟨rfl, rfl⟩ := common.unique earlyCommon
  obtain ⟨rfl, rfl⟩ := setup.unique earlySetup
  have present := pair_tail_root_presence entryRun (by simp [inputPackets]) common setup head tail
  have count : 113 ≤ tailActive.count := by
    rw [tailScope.count, headScope.count, setup.shape.2.1, common.shape.2.1, initialCount]
  obtain ⟨branchWorld, branchActive, branchCost, joinWorld, joinActive, joinCost, final, after, cell, returnCost,
    branchRun, joinRun, returned, empty, separate, fresh, kept⟩ :=
    tail_failure_continuation_complete machine (Recursive.original budget fuel) tailScope present count headsFresh
  have respects := Recursive.original_typed_respects budget fuel
  have sourceTyped := Types.original_run_typed fuel
  have constraints := evaluator_prefix_constraints
  have c0 := common.typed_spec respects sourceTyped initialMachine.valid initialMachine.callersValid initialMachine.wellFormed typed constraints.common
  have c1 := setup.typed_spec respects sourceTyped c0.1 c0.2.1 c0.2.2.1 c0.2.2.2 constraints.miss
  have c2 := head.typed_spec respects sourceTyped c1.1 c1.2.1 c1.2.2.1 c1.2.2.2 constraints.heads
  have headInspection := Derived.scrutinee_complete c2.1 c2.2.1 _ (head_result_scrutinee_source headScope.result) (by intros; trivial)
  obtain ⟨tailCost, tailRun⟩ := tail.exec branchRun
  have recurseTailsRun : Calling.exec (Recursive.original budget fuel) callers recurseTails headWorld headActive =
      some (.next branchWorld branchActive, tailCost) := by rw [recurseTails_actions]; exact tailRun
  have headCasesRun : Calling.exec (Recursive.original budget fuel) callers headCases headWorld headActive =
      some (.next joinWorld joinActive,
        ((Cost.local (1 + (Scrutinee.discriminant (.local 31)).weight)).plus tailCost).plus joinCost) := by
    rw [headCases, Calling.exec_switch, headInspection]
    simp [lookupKey, Control.selectSource, Control.selectIndex, recurseTailsRun, joinRun]
  obtain ⟨headCost, headRun⟩ := head.exec headCasesRun
  have recurseHeadsRun : Calling.exec (Recursive.original budget fuel) callers recurseHeads missWorld missActive =
      some (.next joinWorld joinActive, headCost) := by rw [recurseHeads_actions]; exact headRun
  obtain ⟨casesCost, casesRun⟩ := pair_cases_next missMachine (Recursive.original budget fuel) missScope recurseHeadsRun
  obtain ⟨missCost, missRun⟩ := setup.exec casesRun
  have cacheMissRun : Calling.exec (Recursive.original budget fuel) callers cacheMiss lookupWorld lookupActive =
      some (.next joinWorld joinActive, missCost) := by rw [cacheMiss_actions]; exact missRun
  have lookupRun : Calling.exec (Recursive.original budget fuel) callers lookupSwitch lookupWorld lookupActive =
      some (.returned final after (cell, encodeOutput none foundTable),
        ((Cost.local (1 + (Scrutinee.discriminant (.local 4)).weight)).plus missCost).plus returnCost) := by
    rw [lookupSwitch, Calling.exec_switch, lookupInspection]
    simp [Control.selectSource, Control.selectIndex, cacheMissRun, returned]
  obtain ⟨cost, whole⟩ := common.exec lookupRun
  refine ⟨entered, active, fuel, budget, final, after, cell, cost, entryRun, initialMachine, state, ?_, empty, separate, fresh, kept⟩
  rw [← actual_body, actual_body_common_prefix]
  exact whole

end SubtreeProofs.Rust.SourceEval.Evaluator
