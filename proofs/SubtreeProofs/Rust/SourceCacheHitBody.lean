module

public import SubtreeProofs.Rust.SourceCacheHitContinuation

/-! Parsed native entry and a complete actual cache-hit evaluator body. The
common helper call uses derived finite fuel/readback thresholds; the hit path
and return are constructed without physical-success assumptions. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem entry_hit_body_complete {world : World} {callers : List Activation} {previous : Resources}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (left right : BalancedWord) (table : MemoTable) (leftCell rightCell tableCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord left)))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord right)))
    (tableRead : Readable world.memory world.live tableCell (encodeTable table))
    {owners external : List Nat}
    (input : FieldsFootprint world.memory [leftCell, rightCell, tableCell] owners)
    (frame : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (result : CommonEmbedding) (hit : (LookupEvents.lookup table left right).1 = some result) :
    let packets := inputPackets leftCell rightCell tableCell left right table
    ∃ entered active fuel budget final after cell cost,
      enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount packets = some (entered, active) ∧
      LoanSafeMachine world callers previous external entered active ∧
      active.state = initialState [.reference (encodeWord left), .reference (encodeWord right), encodeTable table] ∧
      Calling.exec (Recursive.original budget fuel) callers body entered active =
        some (.returned final after (cell, encodeOutput (some result) table), cost) ∧
      (∀ slot, after.state slot = .empty) ∧ after.RootsSeparate callers ∧
      (∀ slot binding, after.roots slot = some binding → world.memory.length ≤ binding.address) ∧
      Preserves world final previous.reads := by
  dsimp only
  obtain ⟨entered, active, fuel, budget, middle, current, entryRun, state, count, unbound,
    machine, scope, origins, switchRun, steps⟩ :=
    entry_common_prefix_complete hw hc view left right table leftCell rightCell tableCell leftRead rightRead tableRead input frame covered
  have currentCount : 13 ≤ current.count := by rw [scope.count, count]; decide
  obtain ⟨final, after, cell, last, continuation, empty, separate, fresh, kept⟩ :=
    hit_continuation_complete (scope.query_machine machine origins unbound) (Recursive.original budget fuel)
      scope unbound currentCount result hit
  obtain ⟨cost, whole⟩ := (steps fuel budget (by rfl) (by rfl)).exec continuation
  have bodyRun : Calling.exec (Recursive.original budget fuel) callers body entered active =
      some (.returned final after (cell, encodeOutput (some result) table), cost) := by
    rw [← actual_body, actual_body_common_prefix]; exact whole
  obtain ⟨sameWorld, sameActive, sameEntry, initialMachine, _, _, _, _⟩ :=
    native_entry_machine hw hc view left right table leftCell rightCell tableCell leftRead rightRead tableRead input frame covered
  have same := Prod.mk.inj (Option.some.inj (entryRun.symm.trans sameEntry))
  obtain ⟨rfl, rfl⟩ := same
  exact ⟨_, _, fuel, budget, final, after, cell, cost, entryRun, initialMachine, state, bodyRun, empty, separate, fresh, kept⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
