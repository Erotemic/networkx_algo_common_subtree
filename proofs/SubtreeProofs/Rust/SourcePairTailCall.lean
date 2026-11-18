module

public import SubtreeProofs.Rust.SourcePairTailArguments
public import SubtreeProofs.Rust.SourceOriginalEvaluatorCall

/-! Execute the actual tail recursive call from its constructed native
arguments. The head embedding remains independently owned, while the universal
contract for the smaller tail request supplies only recursive totality. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_tail_call_complete {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {lh lt rh rt : BalancedWord} {table : MemoTable} (scope : TailArgumentScope initial lh lt rh rt table world active)
    {heads : CommonEmbedding} (payload : active.state 37 = Slot.ofValue (encodeResult heads))
    (hole : active.state 31 = headPayloadHole) (count : 47 ≤ active.count) (childTotal : NativeTotal lt rt) :
    ∃ minimumFuel minimumBudget final after result output cost,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      after.state = (nativeCallMasks 44 45 46 (active.forgetRefs (tailCode 13)).state).set 43 (Slot.ofValue (encodeOutput result output)) ∧
      after.state 43 = Slot.ofValue (encodeOutput result output) ∧ after.state 37 = Slot.ofValue (encodeResult heads) ∧
      after.state 31 = headPayloadHole ∧ after.state 32 = .empty ∧ after.state 13 = queryTuple (.Pair lh lt) (.Pair rh rt) ∧
      memoized_common_embedding lt rt table = .ok (result, output) ∧
      (∀ slot binding, slot ≠ 43 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Derived.call (Recursive.original budget fuel) world (active.forgetRefs (tailCode 13)) callers .evaluate (nativeCallArgs 44 45 46) 43 = some (final, after, cost) ∧
        Calling.Prefix (Recursive.original budget fuel) callers (tailCode 14) [.call .evaluate (nativeCallArgs 44 45 46) 43] world active final after := by
  let observed := active.forgetRefs (tailCode 13)
  have machine := h.prepare (tailCode 13)
  have left : observed.state 44 = .shared (encodeWord lt) :=
    (Activation.forgetRefs_observed active (tailCode 13) 44 (by decide +kernel)).trans scope.left
  have right : observed.state 45 = .shared (encodeWord rt) :=
    (Activation.forgetRefs_observed active (tailCode 13) 45 (by decide +kernel)).trans scope.right
  have tableValue : observed.state 46 = Slot.ofValue (encodeTable table) := (h.prepare_closed_local _ 46 (by decide)).trans scope.table
  obtain ⟨root43, bound43, raw43⟩ := scope.result
  obtain ⟨fuel, budget, final, after, result, output, cost, original, roots, countAfter, frameAfter, state, native, memory, stable⟩ :=
    original_evaluator_call_complete machine 44 45 46 43 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intro index member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> change _ < active.count <;> omega)
      lt rt table childTotal left right tableValue bound43 raw43 (LoanEnding.forget_empty _ _ scope.resultEmpty)
  refine ⟨fuel, budget, final, after, result, output, cost, original, roots, countAfter, frameAfter, state, ?_, ?_, ?_, ?_, ?_, native, memory, ?_⟩
  · rw [state]; simp only [Partial.Locals.set, ite_true]
  · rw [state]
    simp only [nativeCallMasks, Partial.Locals.set, show (37 : Nat) ≠ 43 by decide, show (37 : Nat) ≠ 46 by decide,
      show (37 : Nat) ≠ 45 by decide, show (37 : Nat) ≠ 44 by decide, ite_false]
    exact (h.prepare_closed_local _ 37 (by decide)).trans payload
  · rw [state]
    simp only [nativeCallMasks, Partial.Locals.set, show (31 : Nat) ≠ 43 by decide, show (31 : Nat) ≠ 46 by decide,
      show (31 : Nat) ≠ 45 by decide, show (31 : Nat) ≠ 44 by decide, ite_false]
    exact (h.prepare_closed_local _ 31 (by decide)).trans hole
  · rw [state]
    simp only [nativeCallMasks, Partial.Locals.set, show (32 : Nat) ≠ 43 by decide, show (32 : Nat) ≠ 46 by decide,
      show (32 : Nat) ≠ 45 by decide, show (32 : Nat) ≠ 44 by decide, ite_false]
    exact LoanEnding.forget_empty _ _ scope.tableEmpty
  · rw [state]
    simpa [nativeCallMasks, Partial.Locals.set] using prepare_queryTuple scope.tuple (tailCode 13)
  · intro largerFuel largerBudget fuelBound budgetBound
    have actual := stable largerFuel largerBudget fuelBound budgetBound
    exact ⟨actual, .cons (Calling.instruction_call_run actual) (.nil _ _)⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
