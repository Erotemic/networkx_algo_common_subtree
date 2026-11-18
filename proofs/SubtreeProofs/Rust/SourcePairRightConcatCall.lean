module

public import SubtreeProofs.Rust.SourcePairRightConcatArguments

/-! Execute actual right-query concatenation, retire both moved argument roots,
and retain the left witness, matched candidate, table and exact queries.
The temporary original-loan family narrows again after its views end. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_right_concat_call_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [87, 86, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {lh lt rh rt : BalancedWord} {heads tails left : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : RightConcatArgumentScope rh rt world active)
    (payload : RightPayloadScope lh lt rh rt heads tails left table total active) (count : 88 ≤ active.count) :
    ∃ minimumFuel minimumBudget final after, ∃ cost : Cost, ∃ nativeCost : LookupSource.Cost,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      RightPayloadScope lh lt rh rt heads tails left table total after ∧
      after.state 85 = Slot.ofValue (encodeWord (OrderedSolver.appendWord rh rt)) ∧
      (∃ binding, after.roots 85 = some binding) ∧ after.roots 86 = none ∧ after.roots 87 = none ∧
      after.roots = (active.roots.set 87 none).set 86 none ∧ after.count = active.count ∧ after.frame = active.frame ∧
      nativeCost.events = MemoSource.concatenateEvents rh rt ∧
      cost = (Cost.local (Action.call .concatenate (concatenateArgs 86 87) 85).weight).plus (SourceEval.Legacy.costMap nativeCost) ∧
      (∀ slot binding, slot ≠ 85 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers (rightCode 15) ((rightActions.drop 11).take 4) world active final after := by
  let observed := active.forgetRefs (rightCode 11)
  have machine := h.prepare (rightCode 11)
  have left : observed.state 86 = .shared (encodeWord rh) :=
    (Activation.forgetRefs_observed active (rightCode 11) 86 (by decide +kernel)).trans scope.leftValue
  have right : observed.state 87 = .shared (encodeWord rt) :=
    (Activation.forgetRefs_observed active (rightCode 11) 87 (by decide +kernel)).trans scope.rightValue
  obtain ⟨root71, bound71, raw71⟩ := scope.resultRoot
  obtain ⟨fuel, budget, wc, ac, cost, nativeCost, mc, rootsC, countC, frameC, stateC, events, costEq, memoryC, stable⟩ :=
    original_concatenate_complete machine 86 87 85 (by decide) (by decide) (by decide) (by decide)
      (by intro index member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> change _ < active.count <;> omega)
      rh rt left right bound71 raw71 (LoanEnding.forget_empty _ _ scope.resultEmpty)
  obtain ⟨root72, bound72⟩ := scope.bound 86 (by simp)
  obtain ⟨root73, bound73⟩ := scope.bound 87 (by simp)
  have plan : RetirementPlan ac.roots ((rightActions.drop 12).take 2) ((ac.roots.set 87 none).set 86 none) :=
    .dead (by rw [rootsC]; exact bound73) (.dead (binding := root72)
      (by simpa [rootsC, Activation.forgetRefs, Roots.set] using bound72) (.nil _))
  have zero : ZeroRetirement ((rightActions.drop 12).take 2) ac.state := by
    intro slot member
    have selected : slot = 87 ∨ slot = 86 := by simpa [rightActions] using member
    rcases selected with rfl | rfl <;> simp [stateC, Partial.Locals.set, Slot.dropWork]
  let callee := Helpers.callee 0 0
  obtain ⟨final, ar, retirement, mr, rootsR, countR, memoryR⟩ := plan.complete_original callee (rightCode 14) mc rfl zero
  let after := ar.forgetRefs (rightCode 14)
  have fullMachine := mr.prepare (rightCode 14)
  have fake : Calling.Prefix callee callers (rightCode 15) [.fakeRead (.local 85)] final ar final after :=
    .cons (Calling.instruction_noncall_run (act := .fakeRead (.local 85)) rfl) (.nil _ _)
  have last3 : Calling.Prefix callee callers (rightCode 15) ((rightActions.drop 12).take 3) wc ac final after :=
    Calling.Prefix.append (suffix := rightCode 15) (rest := [.fakeRead (.local 85)]) retirement fake
  have stableWhole : ∀ largerFuel largerBudget, fuel ≤ largerFuel → budget ≤ largerBudget →
      Calling.Prefix (Recursive.original largerBudget largerFuel) callers (rightCode 15) ((rightActions.drop 11).take 4) world active final after := by
    intro largerFuel largerBudget fuelBound budgetBound
    have callRun : Calling.Prefix (Recursive.original largerBudget largerFuel) callers (rightCode 12)
        [.call .concatenate (concatenateArgs 86 87) 85] world active wc ac :=
      .cons (Calling.instruction_call_run (stable largerFuel largerBudget fuelBound budgetBound)) (.nil _ _)
    exact Calling.Prefix.append (suffix := rightCode 15) (rest := (rightActions.drop 12).take 3) callRun
      (last3.noncall_callee _ (by decide +kernel))
  have whole := stableWhole fuel budget (by rfl) (by rfl)
  have rootsAfter : after.roots = (active.roots.set 87 none).set 86 none := by
    change ar.roots = _
    rw [rootsR, rootsC]; rfl
  have emptyViews : ∀ slot ∈ [86, 87], after.state slot = .empty := by
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
      by_cases temporary : slot = 86 ∨ slot = 87
      · rcases temporary with rfl | rfl <;> exact ⟨.u32, by rw [emptyViews _ (by simp)]; exact .empty _, .u32⟩
      · exact fullMachine.closed slot (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside temporary ⊢; tauto)
    · intro slot member; exact fullMachine.zero slot (List.mem_cons_of_mem 87 (List.mem_cons_of_mem 86 member))
    · intro slot member; exact fullMachine.origins slot (List.mem_cons_of_mem 87 (List.mem_cons_of_mem 86 member))
  have heldAfter := payload.held.through_prefix whole
    (by intro slot member
        simp only [pairSharedQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
    (by intro slot member
        simp only [pairQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
    (by intro slot member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
    (by intro slot member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [rightActions, keepsRoot])
  refine ⟨fuel, budget, final, after, cost, nativeCost, narrowed, ⟨heldAfter, ?_⟩, ?_,
    ⟨root71, by simpa [rootsAfter, Roots.set] using bound71⟩,
    by simp [rootsAfter, Roots.set], by simp [rootsAfter, Roots.set], rootsAfter,
    countR.trans countC, (last3.shape.1).trans frameC, events, costEq, ?_, stableWhole⟩
  · exact (whole.closed_local_same_calls (index := 75) (by rw [payload.tableValue]; exact ofValue_typed (table_typed table))
      (.adt .table) (by decide +kernel)).trans payload.tableValue
  · have value : ac.state 85 = Slot.ofValue (encodeWord (OrderedSolver.appendWord rh rt)) := by simp [stateC, Partial.Locals.set]
    exact (last3.closed_local_same_calls (index := 85) (by rw [value]; exact ofValue_typed (word_typed (OrderedSolver.appendWord rh rt)))
      (.adt .word) (by decide +kernel)).trans value
  · intro slot binding different root raw memoryRead
    rw [memoryR]; exact memoryC slot binding different root raw memoryRead

end SubtreeProofs.Rust.SourceEval.Evaluator
