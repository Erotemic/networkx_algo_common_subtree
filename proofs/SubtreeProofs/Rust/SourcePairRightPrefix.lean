module

public import SubtreeProofs.Rust.SourcePairRightConcatScope

/-! The first fifteen actual successful-left/right-contraction instructions
transfer the left witness and construct the owned right contraction query. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

structure RightConcatScope (lh lt rh rt : BalancedWord) (heads tails left : CommonEmbedding) (table : MemoTable)
    (total : Aeneas.Std.U32) (active : Activation) : Prop where
  payload : RightPayloadScope lh lt rh rt heads tails left table total active
  wordValue : active.state 85 = Slot.ofValue (encodeWord (OrderedSolver.appendWord rh rt))
  wordBound : ∃ binding, active.roots 85 = some binding
  retired : ∀ slot ∈ [86, 87], active.roots slot = none

theorem pair_right_prefix_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {lh lt rh rt : BalancedWord} {heads tails left : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : PairLeftScope lh lt rh rt heads tails total (some left) table world active)
    (count : 88 ≤ active.count) (unbound : ∀ slot ∈ [82, 85, 86, 87], active.roots slot = none) :
    ∃ minimumFuel minimumBudget final after, ∃ cost : Cost, ∃ nativeCost : LookupSource.Cost,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      RightConcatScope lh lt rh rt heads tails left table total after ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [85, 86, 87] → after.roots slot = active.roots slot) ∧
      nativeCost.events = MemoSource.concatenateEvents rh rt ∧
      cost = (Cost.local (Action.call .concatenate (concatenateArgs 86 87) 85).weight).plus (SourceEval.Legacy.costMap nativeCost) ∧
      (∀ slot binding, slot ≠ 81 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers (rightCode 15) (rightActions.take 15) world active final after := by
  let callee := Helpers.callee 0 0
  obtain ⟨wp, ap, payloadRun, mp, payload, rootsP, countP, frameP, memoryP⟩ :=
    pair_right_payload_complete h callee scope (by omega) (unbound 82 (by simp))
  obtain ⟨fuel, budget, final, after, cost, nativeCost, machine, payloadAfter, value, bound, dead86, dead87,
    countAfter, frameAfter, rootsAfter, events, costEq, memoryAfter, stable⟩ :=
    pair_right_concat_scope_complete mp payload (by rw [countP]; exact count)
      (by intro slot member; rw [rootsP]; exact unbound slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto))
  refine ⟨fuel, budget, final, after, cost, nativeCost, machine, ⟨payloadAfter, value, bound, ?_⟩,
    countAfter.trans countP, frameAfter.trans frameP, ?_, events, costEq, ?_, ?_⟩
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact dead86
    · exact dead87
  · intro slot outside
    rw [rootsAfter slot outside, rootsP]
  · intro slot binding different root raw memoryRead
    exact memoryAfter slot binding (by rw [rootsP]; exact root) raw (memoryP slot binding different root raw memoryRead)
  · intro largerFuel largerBudget fuelBound budgetBound
    exact Calling.Prefix.append (suffix := rightCode 15) (rest := (rightActions.drop 6).take 9)
      (payloadRun.noncall_callee _ (by decide +kernel)) (stable largerFuel largerBudget fuelBound budgetBound)

end SubtreeProofs.Rust.SourceEval.Evaluator
