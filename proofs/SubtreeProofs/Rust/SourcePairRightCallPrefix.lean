module

public import SubtreeProofs.Rust.SourcePairRightCall

/-! Construct the table argument and actual right recursive call as one stable
three-instruction prefix from the original/fresh word-view checkpoint. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_right_call_prefix_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat} {anchor : Resources}
    {lh lt rh rt : BalancedWord} {heads tails leftWitness : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (h : AnchoredLoanMachine before callers previous external [91, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13]
      [92, 93] 85 (OrderedSolver.appendWord rh rt) anchor world active)
    (payload : RightPayloadScope lh lt rh rt heads tails leftWitness table total active)
    (leftView : active.state 91 = .shared (encodeWord (.Pair lh lt)))
    (rightView : active.state 92 = .shared (encodeWord (OrderedSolver.appendWord rh rt)))
    (empty90 : active.state 90 = .empty)
    (root90 : ∃ binding, active.roots 90 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 []))
    (count : 95 ≤ active.count) (unbound : active.roots 94 = none)
    (childTotal : NativeTotal (.Pair lh lt) (OrderedSolver.appendWord rh rt)) :
    ∃ minimumFuel minimumBudget argumentWorld argumentActive final after result output cost,
      AnchoredLoanMachine before callers previous external [91, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13]
        [92, 93] 85 (OrderedSolver.appendWord rh rt) anchor final after ∧
      RightHeldScope lh lt rh rt heads tails leftWitness total after ∧
      after.state 90 = Slot.ofValue (encodeOutput result output) ∧ after.state 75 = .empty ∧
      (∀ slot ∈ [91, 92, 94], after.state slot = .empty) ∧
      memoized_common_embedding (.Pair lh lt) (OrderedSolver.appendWord rh rt) table = .ok (result, output) ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ≠ 94 → after.roots slot = active.roots slot) ∧
      (∀ slot binding, slot ≠ 90 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers (rightCode 24) ((rightActions.drop 22).take 2) world active argumentWorld argumentActive ∧
        Derived.call (Recursive.original budget fuel) argumentWorld (argumentActive.forgetRefs (rightCode 24)) callers
          .evaluate rightContractionArgs 90 = some (final, after, cost) ∧
        Calling.Prefix (Recursive.original budget fuel) callers (rightCode 25) [.call .evaluate rightContractionArgs 90] argumentWorld argumentActive final after ∧
        Calling.Prefix (Recursive.original budget fuel) callers (rightCode 25) ((rightActions.drop 22).take 3) world active final after := by
  obtain ⟨wa, aa, arguments, ma, scopeA, heldA, countA, frameA, rootsA, memoryA⟩ :=
    pair_right_call_arguments_complete h (Helpers.callee 0 0) payload leftView rightView empty90 root90 count unbound
  obtain ⟨fuel, budget, final, after, result, output, cost, machine, heldAfter,
    rootsAfter, countAfter, frameAfter, value, tableMoved, moved, native, _, memoryAfter, stable⟩ :=
    pair_right_call_complete ma scopeA heldA (by rw [countA]; exact count) childTotal
  refine ⟨fuel, budget, wa, aa, final, after, result, output, cost, machine, heldAfter,
    value, tableMoved, moved, native, countAfter.trans countA, frameAfter.trans frameA, ?_, ?_, ?_⟩
  · intro slot outside
    rw [rootsAfter]; exact rootsA slot outside
  · intro slot binding different root raw memoryRead
    have outside : slot ≠ 94 := by intro same; subst slot; rw [unbound] at root; cases root
    exact memoryAfter slot binding different (by rw [rootsA slot outside]; exact root) raw (memoryA slot binding root raw memoryRead)
  · intro largerFuel largerBudget fuelBound budgetBound
    have callRun := stable largerFuel largerBudget fuelBound budgetBound
    have argsRun := arguments.noncall_callee (Recursive.original largerBudget largerFuel) (by decide +kernel)
    exact ⟨argsRun, callRun.1, callRun.2,
      Calling.Prefix.append (suffix := rightCode 25) (rest := [.call .evaluate rightContractionArgs 90]) argsRun callRun.2⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
