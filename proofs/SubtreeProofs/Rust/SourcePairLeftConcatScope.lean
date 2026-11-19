module

public import SubtreeProofs.Rust.SourcePairLeftConcatCall

/-! Construct all nine actual instructions from matched construction through
the owned left contraction query. Native query views and the candidate persist. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_left_concat_scope_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {lh lt rh rt : BalancedWord} {heads tails : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (queries : PairQueryScope lh lt rh rt active) (candidate : MatchedScope heads tails table total active)
    (count : 74 ≤ active.count) (unbound : ∀ slot ∈ [71, 72, 73], active.roots slot = none) :
    ∃ minimumFuel minimumBudget final after, ∃ cost : Cost, ∃ nativeCost : LookupSource.Cost,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      PairQueryScope lh lt rh rt after ∧ MatchedScope heads tails table total after ∧
      after.state 71 = Slot.ofValue (encodeWord (OrderedSolver.appendWord lh lt)) ∧
      (∃ binding, after.roots 71 = some binding) ∧ after.roots 72 = none ∧ after.roots 73 = none ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [71, 72, 73] → after.roots slot = active.roots slot) ∧
      nativeCost.events = MemoSource.concatenateEvents lh lt ∧
      cost = (Cost.local (Action.call .concatenate (concatenateArgs 72 73) 71).weight).plus (SourceEval.Legacy.costMap nativeCost) ∧
      (∀ slot binding, active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 39) ((matchedActions.drop 30).take 9) world active final after := by
  let callee := Helpers.callee 0 0
  obtain ⟨wa, aa, arguments, ma, scopeA, queriesA, candidateA, countA, frameA, rootsA, memoryA⟩ :=
    pair_left_concat_arguments_complete h callee queries candidate count unbound
  obtain ⟨fuel, budget, final, after, cost, nativeCost, machine, queriesAfter, candidateAfter, value, bound, dead72, dead73,
    rootsAfter, countAfter, frameAfter, events, costEq, memoryAfter, stable⟩ :=
    pair_left_concat_call_complete ma scopeA queriesA candidateA (by rw [countA]; exact count)
  refine ⟨fuel, budget, final, after, cost, nativeCost, machine, queriesAfter, candidateAfter, value, bound, dead72, dead73,
    countAfter.trans countA, frameAfter.trans frameA, ?_, events, costEq, ?_, ?_⟩
  · intro slot outside
    have different : slot ≠ 71 ∧ slot ≠ 72 ∧ slot ≠ 73 := by simpa using outside
    simpa only [rootsAfter, Roots.set, different.2.1, different.2.2, ite_false] using rootsA slot outside
  · intro slot binding root raw memoryRead
    have old : slot ∉ [71, 72, 73] := by intro member; rw [unbound slot member] at root; cases root
    have not71 : slot ≠ 71 := by intro same; subst slot; exact old (by simp)
    exact memoryAfter slot binding not71 (by rw [rootsA slot old]; exact root) raw (memoryA slot binding root raw memoryRead)
  · intro largerFuel largerBudget fuelBound budgetBound
    exact Calling.Prefix.append (suffix := matchedCode 39) (rest := (matchedActions.drop 35).take 4)
      (arguments.noncall_callee _ (by decide +kernel)) (stable largerFuel largerBudget fuelBound budgetBound)

end SubtreeProofs.Rust.SourceEval.Evaluator
