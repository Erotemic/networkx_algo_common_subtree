module

public import SubtreeProofs.Rust.SourceEmptyRouting
public import SubtreeProofs.Rust.SourceRecursiveBudget

/-! Parsed native evaluator entry, common lookup, miss setup, selected empty
branch and return compose at a shared sufficient fuel/readback pair. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem entry_empty_body_complete {world : World} {callers : List Activation} {previous : Resources}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (left right : BalancedWord) (table : MemoTable) (leftCell rightCell tableCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord left)))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord right)))
    (tableRead : Readable world.memory world.live tableCell (encodeTable table))
    {owners external : List Nat}
    (input : FieldsFootprint world.memory [leftCell, rightCell, tableCell] owners)
    (frame : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (hempty : left = .Empty ∨ right = .Empty) (miss : MemoizedOrderedSolver.findResult table left right = none) :
    let packets := inputPackets leftCell rightCell tableCell left right table
    ∃ entered active fuel budget final after cell cost,
      enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount packets = some (entered, active) ∧
      LoanSafeMachine world callers previous external entered active ∧
      active.state = initialState [.reference (encodeWord left), .reference (encodeWord right), encodeTable table] ∧
      Calling.exec (Recursive.original budget fuel) callers body entered active =
        some (.returned final after (cell, encodeOutput (some emptyWitness) (.Entry ⟨left, right, emptyWitness⟩ table)), cost) ∧
      (∀ slot, after.state slot = .empty) ∧ after.RootsSeparate callers ∧
      (∀ slot binding, after.roots slot = some binding → world.memory.length ≤ binding.address) ∧
      Preserves world final previous.reads := by
  dsimp only
  obtain ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, middle, current, entryRun, unbound,
    machine, scope, queries, tupleOrigin, closed, words, lookupInspection, _, _, prefixes⟩ :=
    entry_miss_setup_complete hw hc view left right table leftCell rightCell tableCell leftRead rightRead tableRead input frame covered miss
  obtain ⟨sameWorld, sameActive, sameEntry, initialMachine, state, count, _, _⟩ :=
    native_entry_machine hw hc view left right table leftCell rightCell tableCell leftRead rightRead tableRead input frame covered
  have same := Prod.mk.inj (Option.some.inj (entryRun.symm.trans sameEntry))
  obtain ⟨rfl, rfl⟩ := same
  obtain ⟨branchFuel, branchBudget, final, after, cell, branchCost, branch, empty, separate, fresh, kept⟩ :=
    empty_branch_complete (scope.original_machine machine closed queries tupleOrigin) scope unbound (by rw [scope.count, count]; decide)
  let fuel := max minFuel branchFuel
  let budget := max minBudget branchBudget
  have largerBranch : Calling.exec (Recursive.original budget fuel) callers emptyLeft middle current =
      some (.returned final after (cell, encodeOutput (some emptyWitness) (.Entry ⟨left, right, emptyWitness⟩ table)), branchCost) :=
    Calling.exec_extends (fun _ _ _ _ _ _ _ _ run => Recursive.original_enlarge (Nat.le_max_right _ _) (Nat.le_max_right _ _) run) branch
  obtain ⟨casesCost, casesRun⟩ := empty_cases_complete machine (Recursive.original budget fuel) scope hempty largerBranch
  obtain ⟨common, setup⟩ := prefixes fuel budget (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  obtain ⟨missCost, missRun⟩ := setup.exec casesRun
  have cacheMissRun : Calling.exec (Recursive.original budget fuel) callers cacheMiss lookupWorld lookupActive =
      some (.returned final after (cell, encodeOutput (some emptyWitness) (.Entry ⟨left, right, emptyWitness⟩ table)), missCost) := by
    rw [cacheMiss_actions]; exact missRun
  have switchRun : Calling.exec (Recursive.original budget fuel) callers lookupSwitch lookupWorld lookupActive =
      some (.returned final after (cell, encodeOutput (some emptyWitness) (.Entry ⟨left, right, emptyWitness⟩ table)),
        (Cost.local (1 + (Scrutinee.discriminant (.local 4)).weight)).plus missCost) := by
    rw [lookupSwitch, Calling.exec_switch, lookupInspection]
    simp [Control.selectSource, Control.selectIndex, cacheMissRun]
  obtain ⟨cost, whole⟩ := common.exec switchRun
  refine ⟨_, _, fuel, budget, final, after, cell, cost, entryRun, initialMachine, state, ?_, empty, separate, fresh, kept⟩
  rw [← actual_body, actual_body_common_prefix]
  exact whole

end SubtreeProofs.Rust.SourceEval.Evaluator
