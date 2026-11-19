module

public import SubtreeProofs.Rust.SourcePairLeftCall

/-! Construct all remaining left-call arguments and the actual recursive call
as one stable five-instruction prefix from the fresh word-view checkpoint. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_left_call_prefix_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat} {anchor : Resources}
    {lh lt rh rt : BalancedWord} {heads tails : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (h : AnchoredLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13]
      [77, 78] 71 (OrderedSolver.appendWord lh lt) anchor world active)
    (queries : PairQueryScope lh lt rh rt active) (candidate : MatchedScope heads tails table total active)
    (left : active.state 77 = .shared (encodeWord (OrderedSolver.appendWord lh lt)))
    (empty76 : active.state 76 = .empty)
    (root76 : ∃ binding, active.roots 76 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 []))
    (count : 81 ≤ active.count) (unbound : ∀ slot ∈ [79, 80], active.roots slot = none)
    (childTotal : NativeTotal (OrderedSolver.appendWord lh lt) (.Pair rh rt)) :
    ∃ minimumFuel minimumBudget argumentWorld argumentActive final after result output cost,
      AnchoredLoanMachine before callers previous external [79, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13]
        [77, 78] 71 (OrderedSolver.appendWord lh lt) anchor final after ∧
      PairQueryScope lh lt rh rt after ∧ MatchedCandidateScope heads tails total after ∧
      after.state 76 = Slot.ofValue (encodeOutput result output) ∧ after.state 42 = .empty ∧
      (∀ slot ∈ [77, 79, 80], after.state slot = .empty) ∧
      memoized_common_embedding (OrderedSolver.appendWord lh lt) (.Pair rh rt) table = .ok (result, output) ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [79, 80] → after.roots slot = active.roots slot) ∧
      (∀ slot binding, slot ≠ 76 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 48) ((matchedActions.drop 44).take 4) world active argumentWorld argumentActive ∧
        Derived.call (Recursive.original budget fuel) argumentWorld (argumentActive.forgetRefs (matchedCode 48)) callers
          .evaluate leftContractionArgs 76 = some (final, after, cost) ∧
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 49) [.call .evaluate leftContractionArgs 76] argumentWorld argumentActive final after ∧
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 49) ((matchedActions.drop 44).take 5) world active final after := by
  obtain ⟨wa, aa, arguments, ma, scopeA, queriesA, candidateA, countA, frameA, rootsA, memoryA⟩ :=
    pair_left_call_arguments_complete h (Helpers.callee 0 0) queries candidate left empty76 root76 count unbound
  obtain ⟨fuel, budget, final, after, result, output, cost, machine, queriesAfter, candidateAfter,
    rootsAfter, countAfter, frameAfter, value, tableMoved, moved, native, _, memoryAfter, stable⟩ :=
    pair_left_call_complete ma scopeA queriesA candidateA (by rw [countA]; exact count) childTotal
  refine ⟨fuel, budget, wa, aa, final, after, result, output, cost, machine, queriesAfter, candidateAfter,
    value, tableMoved, moved, native, countAfter.trans countA, frameAfter.trans frameA, ?_, ?_, ?_⟩
  · intro slot outside
    rw [rootsAfter]; exact rootsA slot outside
  · intro slot binding different root raw memoryRead
    have outside : slot ∉ [79, 80] := by intro member; rw [unbound slot member] at root; cases root
    exact memoryAfter slot binding different (by rw [rootsA slot outside]; exact root) raw (memoryA slot binding root raw memoryRead)
  · intro largerFuel largerBudget fuelBound budgetBound
    have callRun := stable largerFuel largerBudget fuelBound budgetBound
    have argsRun := arguments.noncall_callee (Recursive.original largerBudget largerFuel) (by decide +kernel)
    exact ⟨argsRun, callRun.1, callRun.2,
      Calling.Prefix.append (suffix := matchedCode 49) (rest := [.call .evaluate leftContractionArgs 76]) argsRun callRun.2⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
