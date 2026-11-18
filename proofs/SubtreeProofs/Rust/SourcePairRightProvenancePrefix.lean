module

public import SubtreeProofs.Rust.SourcePairRightPrefix
public import SubtreeProofs.Rust.SourcePairRightFreshPayload
public import SubtreeProofs.Rust.SourcePairRightConcatProvenanceScope

/-! All fifteen real successful-left/right-query instructions retain both
witness bounds and derive bounds for both owned contraction words. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_right_prefix_complete_provenance {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {lh lt rh rt : BalancedWord} {heads tails left : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : PairLeftScope lh lt rh rt heads tails total (some left) table world active)
    (leftAbove : LocalOwnersAbove before.memory.length world active 74)
    (candidateAbove : LocalOwnersAbove before.memory.length world active 64)
    (wordAbove : LocalOwnersAbove before.memory.length world active 71)
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
      (∀ slot ∈ [64, 71, 81, 85], LocalOwnersAbove before.memory.length final after slot) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers (rightCode 15) (rightActions.take 15) world active final after := by
  let callee := Helpers.callee 0 0
  obtain ⟨wp, ap, payloadRun, mp, payload, rootsP, countP, frameP, leftP, candidateP, wordP, memoryP⟩ :=
    pair_right_payload_complete_fresh h callee scope leftAbove candidateAbove wordAbove (by omega) (unbound 82 (by simp))
  obtain ⟨fuel, budget, final, after, cost, nativeCost, machine, payloadAfter, value, bound, dead86, dead87,
    countAfter, frameAfter, rootsAfter, events, costEq, memoryAfter, heldFinal, rightWordFinal, stable⟩ :=
    pair_right_concat_scope_complete_provenance mp payload (by
      intro slot member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact candidateP
      · exact wordP
      · exact leftP) (by rw [countP]; exact count)
      (by intro slot member; rw [rootsP]; exact unbound slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto))
  refine ⟨fuel, budget, final, after, cost, nativeCost, machine, ⟨payloadAfter, value, bound, ?_⟩,
    countAfter.trans countP, frameAfter.trans frameP, ?_, events, costEq, ?_, ?_, ?_⟩
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact dead86
    · exact dead87
  · intro slot outside
    rw [rootsAfter slot outside, rootsP]
  · intro slot binding different root raw memoryRead
    exact memoryAfter slot binding (by rw [rootsP]; exact root) raw (memoryP slot binding different root raw memoryRead)
  · intro slot member
    have selected : slot ∈ [64, 71, 81] ∨ slot = 85 := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] using member
    rcases selected with old | rfl
    · exact heldFinal slot old
    · exact rightWordFinal
  · intro largerFuel largerBudget fuelBound budgetBound
    exact Calling.Prefix.append (suffix := rightCode 15) (rest := (rightActions.drop 6).take 9)
      (payloadRun.noncall_callee _ (by decide +kernel)) (stable largerFuel largerBudget fuelBound budgetBound)

end SubtreeProofs.Rust.SourceEval.Evaluator
