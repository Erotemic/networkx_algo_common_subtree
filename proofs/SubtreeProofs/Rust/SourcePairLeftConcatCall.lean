module

public import SubtreeProofs.Rust.SourcePairLeftConcatArguments

/-! Execute actual left-query concatenation, retire both moved argument roots,
and retain the owned appended word with the matched candidate and exact queries.
The temporary original-loan family narrows again after its views end. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_left_concat_call_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [73, 72, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {lh lt rh rt : BalancedWord} {heads tails : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : LeftConcatArgumentScope lh lt world active) (queries : PairQueryScope lh lt rh rt active)
    (candidate : MatchedScope heads tails table total active) (count : 74 ≤ active.count) :
    ∃ minimumFuel minimumBudget final after, ∃ cost : Cost, ∃ nativeCost : LookupSource.Cost,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      PairQueryScope lh lt rh rt after ∧ MatchedScope heads tails table total after ∧
      after.state 71 = Slot.ofValue (encodeWord (OrderedSolver.appendWord lh lt)) ∧
      (∃ binding, after.roots 71 = some binding) ∧ after.roots 72 = none ∧ after.roots 73 = none ∧
      after.roots = (active.roots.set 73 none).set 72 none ∧ after.count = active.count ∧ after.frame = active.frame ∧
      nativeCost.events = MemoSource.concatenateEvents lh lt ∧
      cost = (Cost.local (Action.call .concatenate (concatenateArgs 72 73) 71).weight).plus (SourceEval.Legacy.costMap nativeCost) ∧
      (∀ slot binding, slot ≠ 71 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 39) ((matchedActions.drop 35).take 4) world active final after := by
  let observed := active.forgetRefs (matchedCode 35)
  have machine := h.prepare (matchedCode 35)
  have left : observed.state 72 = .shared (encodeWord lh) :=
    (Activation.forgetRefs_observed active (matchedCode 35) 72 (by decide +kernel)).trans scope.leftValue
  have right : observed.state 73 = .shared (encodeWord lt) :=
    (Activation.forgetRefs_observed active (matchedCode 35) 73 (by decide +kernel)).trans scope.rightValue
  obtain ⟨root71, bound71, raw71⟩ := scope.resultRoot
  obtain ⟨fuel, budget, wc, ac, cost, nativeCost, mc, rootsC, countC, frameC, stateC, events, costEq, memoryC, stable⟩ :=
    original_concatenate_complete machine 72 73 71 (by decide) (by decide) (by decide) (by decide)
      (by intro index member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> change _ < active.count <;> omega)
      lh lt left right bound71 raw71 (LoanEnding.forget_empty _ _ scope.resultEmpty)
  obtain ⟨root72, bound72⟩ := scope.bound 72 (by simp)
  obtain ⟨root73, bound73⟩ := scope.bound 73 (by simp)
  have plan : RetirementPlan ac.roots ((matchedActions.drop 36).take 2) ((ac.roots.set 73 none).set 72 none) :=
    .dead (by rw [rootsC]; exact bound73) (.dead (binding := root72)
      (by simpa [rootsC, Activation.forgetRefs, Roots.set] using bound72) (.nil _))
  have zero : ZeroRetirement ((matchedActions.drop 36).take 2) ac.state := by
    intro slot member
    have selected : slot = 73 ∨ slot = 72 := by simpa [matchedActions] using member
    rcases selected with rfl | rfl <;> simp [stateC, Partial.Locals.set, Slot.dropWork]
  let callee := Helpers.callee 0 0
  obtain ⟨final, ar, retirement, mr, rootsR, countR, memoryR⟩ := plan.complete_original callee (matchedCode 38) mc rfl zero
  let after := ar.forgetRefs (matchedCode 38)
  have fullMachine := mr.prepare (matchedCode 38)
  have fake : Calling.Prefix callee callers (matchedCode 39) [.fakeRead (.local 71)] final ar final after :=
    .cons (Calling.instruction_noncall_run (act := .fakeRead (.local 71)) rfl) (.nil _ _)
  have last3 : Calling.Prefix callee callers (matchedCode 39) ((matchedActions.drop 36).take 3) wc ac final after :=
    Calling.Prefix.append (suffix := matchedCode 39) (rest := [.fakeRead (.local 71)]) retirement fake
  have stableWhole : ∀ largerFuel largerBudget, fuel ≤ largerFuel → budget ≤ largerBudget →
      Calling.Prefix (Recursive.original largerBudget largerFuel) callers (matchedCode 39) ((matchedActions.drop 35).take 4) world active final after := by
    intro largerFuel largerBudget fuelBound budgetBound
    have callRun : Calling.Prefix (Recursive.original largerBudget largerFuel) callers (matchedCode 36)
        [.call .concatenate (concatenateArgs 72 73) 71] world active wc ac :=
      .cons (Calling.instruction_call_run (stable largerFuel largerBudget fuelBound budgetBound)) (.nil _ _)
    exact Calling.Prefix.append (suffix := matchedCode 39) (rest := (matchedActions.drop 36).take 3) callRun
      (last3.noncall_callee _ (by decide +kernel))
  have whole := stableWhole fuel budget (by rfl) (by rfl)
  have rootsAfter : after.roots = (active.roots.set 73 none).set 72 none := by
    change ar.roots = _
    rw [rootsR, rootsC]; rfl
  have emptyViews : ∀ slot ∈ [72, 73], after.state slot = .empty := by
    intro slot member
    have missing : after.roots slot = none := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp [rootsAfter, Roots.set]
    obtain ⟨_, _, frame⟩ := fullMachine.native.valid
    have slotFrame := frame.slots slot
    change (match after.roots slot with
      | none => after.state slot = .empty
      | some binding => Anchored final after.frame slot binding (after.state slot) _) at slotFrame
    simpa only [missing] using slotFrame
  have narrowed : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after := by
    refine ⟨fullMachine.native, ?_, ?_, ?_⟩
    · intro slot outside
      by_cases temporary : slot = 72 ∨ slot = 73
      · rcases temporary with rfl | rfl <;> exact ⟨.u32, by rw [emptyViews _ (by simp)]; exact .empty _, .u32⟩
      · exact fullMachine.closed slot (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside temporary ⊢; tauto)
    · intro slot member; exact fullMachine.zero slot (List.mem_cons_of_mem 73 (List.mem_cons_of_mem 72 member))
    · intro slot member; exact fullMachine.origins slot (List.mem_cons_of_mem 73 (List.mem_cons_of_mem 72 member))
  have queryAfter : PairQueryScope lh lt rh rt after := by
    apply prefix_pair_queries_complete whole queries
    · intro slot member
      simp only [pairSharedQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    · intro slot member
      simp only [pairQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  refine ⟨fuel, budget, final, after, cost, nativeCost, narrowed, queryAfter, ?_, ?_,
    ⟨root71, by simpa [rootsAfter, Roots.set] using bound71⟩,
    by simp [rootsAfter, Roots.set], by simp [rootsAfter, Roots.set], rootsAfter,
    countR.trans countC, (last3.shape.1).trans frameC, events, costEq, ?_, stableWhole⟩
  · refine ⟨(whole.closed_local_same_calls (index := 37) (by rw [candidate.headHole]; exact resultWordHole_typed heads.edges)
        (.adt .embedding) (by decide +kernel)).trans candidate.headHole,
      (whole.closed_local_same_calls (index := 47) (by rw [candidate.tailHole]; exact resultWordHole_typed tails.edges)
        (.adt .embedding) (by decide +kernel)).trans candidate.tailHole,
      (whole.closed_local_same_calls (index := 42) (by rw [candidate.tableValue]; exact ofValue_typed (table_typed table))
        (.adt .table) (by decide +kernel)).trans candidate.tableValue,
      (whole.closed_local_same_calls (index := 58) (by rw [candidate.totalValue]; exact .number total.hmax)
        .u32 (by decide +kernel)).trans candidate.totalValue,
      (whole.closed_local_same_calls (index := 64) (by rw [candidate.candidate]; exact ofValue_typed (result_typed (matchedWitness heads tails total)))
        (.adt .embedding) (by decide +kernel)).trans candidate.candidate, ?_⟩
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp only [rootsAfter, Roots.set] <;> exact candidate.retired _ (by simp)
  · have value : ac.state 71 = Slot.ofValue (encodeWord (OrderedSolver.appendWord lh lt)) := by simp [stateC, Partial.Locals.set]
    exact (last3.closed_local_same_calls (index := 71) (by rw [value]; exact ofValue_typed (word_typed (OrderedSolver.appendWord lh lt)))
      (.adt .word) (by decide +kernel)).trans value
  · intro slot binding different root raw memoryRead
    rw [memoryR]; exact memoryC slot binding different root raw memoryRead

end SubtreeProofs.Rust.SourceEval.Evaluator
