module

public import SubtreeProofs.Rust.SourcePairRightConcatProvenanceCall

/-! Construct all nine actual right concatenation instructions while retaining
the left witness, matched candidate, native table and original queries. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_right_concat_scope_complete_provenance {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {lh lt rh rt : BalancedWord} {heads tails left : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (payload : RightPayloadScope lh lt rh rt heads tails left table total active)
    (heldAbove : ∀ slot ∈ [64, 71, 81], LocalOwnersAbove before.memory.length world active slot)
    (count : 88 ≤ active.count) (unbound : ∀ slot ∈ [85, 86, 87], active.roots slot = none) :
    ∃ minimumFuel minimumBudget final after, ∃ cost : Cost, ∃ nativeCost : LookupSource.Cost,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      RightPayloadScope lh lt rh rt heads tails left table total after ∧
      after.state 85 = Slot.ofValue (encodeWord (OrderedSolver.appendWord rh rt)) ∧
      (∃ binding, after.roots 85 = some binding) ∧ after.roots 86 = none ∧ after.roots 87 = none ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [85, 86, 87] → after.roots slot = active.roots slot) ∧
      nativeCost.events = MemoSource.concatenateEvents rh rt ∧
      cost = (Cost.local (Action.call .concatenate (concatenateArgs 86 87) 85).weight).plus (SourceEval.Legacy.costMap nativeCost) ∧
      (∀ slot binding, active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      (∀ slot ∈ [64, 71, 81], LocalOwnersAbove before.memory.length final after slot) ∧
      LocalOwnersAbove before.memory.length final after 85 ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers (rightCode 15) ((rightActions.drop 6).take 9) world active final after := by
  let callee := Helpers.callee 0 0
  obtain ⟨wa, aa, arguments, ma, scopeA, payloadA, countA, frameA, rootsA, memoryA⟩ :=
    pair_right_concat_arguments_complete h callee payload count unbound
  have heldA : ∀ slot ∈ [64, 71, 81], LocalOwnersAbove before.memory.length wa aa slot := by
    intro slot member
    exact arguments.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide +kernel))
      h.native.valid h.native.callersValid h.native.wellFormed (heldAbove slot member)
  obtain ⟨fuel, budget, final, after, cost, nativeCost, machine, payloadAfter, value, bound, dead72, dead73,
    rootsAfter, countAfter, frameAfter, events, costEq, memoryAfter, heldFinal, wordFinal, stable⟩ :=
    pair_right_concat_call_complete_provenance ma scopeA payloadA heldA (by rw [countA]; exact count)
  refine ⟨fuel, budget, final, after, cost, nativeCost, machine, payloadAfter, value, bound, dead72, dead73,
    countAfter.trans countA, frameAfter.trans frameA, ?_, events, costEq, ?_, heldFinal, wordFinal, ?_⟩
  · intro slot outside
    have different : slot ≠ 85 ∧ slot ≠ 86 ∧ slot ≠ 87 := by simpa using outside
    simpa only [rootsAfter, Roots.set, different.2.1, different.2.2, ite_false] using rootsA slot outside
  · intro slot binding root raw memoryRead
    have old : slot ∉ [85, 86, 87] := by intro member; rw [unbound slot member] at root; cases root
    have not71 : slot ≠ 85 := by intro same; subst slot; exact old (by simp)
    exact memoryAfter slot binding not71 (by rw [rootsA slot old]; exact root) raw (memoryA slot binding root raw memoryRead)
  · intro largerFuel largerBudget fuelBound budgetBound
    exact Calling.Prefix.append (suffix := rightCode 15) (rest := (rightActions.drop 11).take 4)
      (arguments.noncall_callee _ (by decide +kernel)) (stable largerFuel largerBudget fuelBound budgetBound)

end SubtreeProofs.Rust.SourceEval.Evaluator
