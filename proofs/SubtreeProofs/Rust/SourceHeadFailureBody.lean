module

public import SubtreeProofs.Rust.SourceHeadFailureContinuation
public import SubtreeProofs.Rust.SourcePairNextRouting

/-! Complete actual parsed evaluator body when the smaller head request returns
None. Independent native head failure selects this path; entry, every head
instruction, output packing, joins and parent return are constructed. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem entry_head_failure_body_complete {world : World} {callers : List Activation} {previous : Resources}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (lh lt rh rt : BalancedWord) (table headOutput : MemoTable) (leftCell rightCell tableCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord (.Pair lh lt))))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord (.Pair rh rt))))
    (tableRead : Readable world.memory world.live tableCell (encodeTable table))
    {owners external : List Nat}
    (input : FieldsFootprint world.memory [leftCell, rightCell, tableCell] owners)
    (frame : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (miss : MemoizedOrderedSolver.findResult table (.Pair lh lt) (.Pair rh rt) = none)
    (childTotal : NativeTotal lh rh) (headFailure : memoized_common_embedding lh rh table = .ok (none, headOutput)) :
    let packets := inputPackets leftCell rightCell tableCell (.Pair lh lt) (.Pair rh rt) table
    ∃ entered active fuel budget final after cell cost,
      enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount packets = some (entered, active) ∧
      LoanSafeMachine world callers previous external entered active ∧
      active.state = initialState [.reference (encodeWord (.Pair lh lt)), .reference (encodeWord (.Pair rh rt)), encodeTable table] ∧
      Calling.exec (Recursive.original budget fuel) callers body entered active =
        some (.returned final after (cell, encodeOutput none headOutput), cost) ∧
      (∀ slot, after.state slot = .empty) ∧ after.RootsSeparate callers ∧
      (∀ slot binding, after.roots slot = some binding → world.memory.length ≤ binding.address) ∧
      Preserves world final previous.reads := by
  dsimp only
  obtain ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, entryRun, unbound,
    machine, scope, queries, tupleOrigin, closed, words, lookupInspection, inspectLeft, inspectRight, prefixes⟩ :=
    entry_miss_setup_complete hw hc view (.Pair lh lt) (.Pair rh rt) table leftCell rightCell tableCell
      leftRead rightRead tableRead input frame covered miss
  obtain ⟨sameWorld, sameActive, sameEntry, initialMachine, state, count, _, _⟩ :=
    native_entry_machine hw hc view (.Pair lh lt) (.Pair rh rt) table leftCell rightCell tableCell
      leftRead rightRead tableRead input frame covered
  have same := Prod.mk.inj (Option.some.inj (entryRun.symm.trans sameEntry))
  obtain ⟨rfl, rfl⟩ := same
  obtain ⟨headFuel, headBudget, headWorld, headActive, headResult, output, headMachine, headScope, headNative, heads⟩ :=
    pair_head_scope_complete (scope.original_machine machine closed queries tupleOrigin) scope unbound
      (by rw [scope.count, count]; decide) childTotal
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (headNative.symm.trans headFailure))
  let fuel := max minFuel headFuel
  let budget := max minBudget headBudget
  have support : ∀ slot, slot ∉ [0, 1, 2, 3, 13] → missActive.roots slot = none := by
    intro slot outside
    rw [scope.otherRoots slot (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto)]
    apply unbound slot
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto
  obtain ⟨root3, bound3⟩ := Activation.root_of_materialize machine.valid (by rw [scope.inputs.table]; exact Slot.materialize_ofValue _)
  have bound3Head : headActive.roots 3 = some root3 := by rw [headScope.otherRoots 3 (by decide)]; exact bound3
  obtain ⟨branchWorld, branchActive, branchCost, final, after, cell, returnCost, branch, returned, empty, separate, fresh, kept⟩ :=
    head_failure_continuation_complete headMachine (Recursive.original budget fuel) headScope support
      (by rw [headScope.count, scope.count, count]; decide) bound3Head
  obtain ⟨headCost, headRun⟩ := (heads fuel budget (Nat.le_max_right _ _) (Nat.le_max_right _ _)).exec branch
  have headBranch : Calling.exec (Recursive.original budget fuel) callers recurseHeads missWorld missActive =
      some (.next branchWorld branchActive, headCost) := by rw [recurseHeads_actions]; exact headRun
  obtain ⟨casesCost, casesRun⟩ := pair_cases_next machine (Recursive.original budget fuel) scope headBranch
  obtain ⟨common, setup⟩ := prefixes fuel budget (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  obtain ⟨missCost, missRun⟩ := setup.exec casesRun
  have cacheMissRun : Calling.exec (Recursive.original budget fuel) callers cacheMiss lookupWorld lookupActive =
      some (.next branchWorld branchActive, missCost) := by rw [cacheMiss_actions]; exact missRun
  have switchRun : Calling.exec (Recursive.original budget fuel) callers lookupSwitch lookupWorld lookupActive =
      some (.returned final after (cell, encodeOutput none output),
        ((Cost.local (1 + (Scrutinee.discriminant (.local 4)).weight)).plus missCost).plus returnCost) := by
    rw [lookupSwitch, Calling.exec_switch, lookupInspection]
    simp [Control.selectSource, Control.selectIndex, cacheMissRun, returned]
  obtain ⟨cost, whole⟩ := common.exec switchRun
  refine ⟨_, _, fuel, budget, final, after, cell, cost, entryRun, initialMachine, state, ?_, empty, separate, fresh, kept⟩
  rw [← actual_body, actual_body_common_prefix]
  exact whole

end SubtreeProofs.Rust.SourceEval.Evaluator
