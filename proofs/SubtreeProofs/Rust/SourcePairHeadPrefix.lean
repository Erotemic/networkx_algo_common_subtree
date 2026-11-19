module

public import SubtreeProofs.Rust.SourcePairHeadCall
import Mathlib.Tactic.IntervalCases

/-! Compose the actual pair-child views, head-call argument setup and recursive
head call. Every caller-side instruction/permission is constructed; only the
universal contract for the strictly smaller head request is supplied. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_head_prefix_complete {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [1, 2, 13] world active)
    {lh lt rh rt : BalancedWord} {table : MemoTable} (scope : MissScope initial (.Pair lh lt) (.Pair rh rt) table world active)
    (unbound : ∀ slot, slot ∉ [1, 2, 3] → initial.roots slot = none) (count : 37 ≤ active.count)
    (childTotal : NativeTotal lh rh) :
    ∃ minimumFuel minimumBudget final after result output,
      OriginalLoanMachine before callers previous external [35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      after.state 33 = Slot.ofValue (encodeOutput result output) ∧
      after.state 13 = queryTuple (.Pair lh lt) (.Pair rh rt) ∧
      after.state 1 = .shared (encodeWord (.Pair lh lt)) ∧ after.state 2 = .shared (encodeWord (.Pair rh rt)) ∧
      after.state 3 = .empty ∧ after.state 0 = .empty ∧
      after.state 27 = .shared (.boxed (encodeWord lh)) ∧ after.state 28 = .shared (.boxed (encodeWord lt)) ∧
      after.state 29 = .shared (.boxed (encodeWord rh)) ∧ after.state 30 = .shared (.boxed (encodeWord rt)) ∧
      memoized_common_embedding lh rh table = .ok (result, output) ∧
      (∀ slot ∈ [34, 35, 36], after.state slot = .empty) ∧
      (∀ slot ∈ [27, 28, 29, 30, 33, 34, 35, 36], ∃ binding, after.roots slot = some binding) ∧
      (∀ slot, slot ∉ [27, 28, 29, 30, 33, 34, 35, 36] → after.roots slot = active.roots slot) ∧
      (∀ slot binding, active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers (headCode 16) (headActions.take 16) world active final after := by
  let callee := Helpers.callee 0 0
  obtain ⟨wv, av, views, mv, countV, frameV, liveV, otherV, tupleV, tableV, leftV, leftTailV, rightV, rightTailV, memoryV⟩ :=
    pair_head_views_complete h callee scope unbound (by omega)
  have unboundV : ∀ slot ∈ [33, 34, 35, 36], av.roots slot = none := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> rw [otherV _ (by decide), scope.otherRoots _ (by decide)] <;> exact unbound _ (by decide)
  obtain ⟨wa, aa, arguments, ma, argumentScope, memoryA⟩ :=
    pair_head_arguments_complete mv callee tupleV leftV rightV tableV (by rw [countV]; exact count) unboundV
  obtain ⟨fuel, budget, final, after, result, output, cost, machine, rootsAfter, countAfter, frameAfter, valueAfter, tupleAfter,
    emptyAfter, native, statesAfter, memoryAfter, callRun⟩ :=
    pair_head_call_complete ma argumentScope (by rw [argumentScope.count, countV]; exact count) childTotal
  have first15 : Calling.Prefix callee callers (headCode 15) (headActions.take 15) world active wa aa :=
    Calling.Prefix.append (suffix := headCode 15) (rest := (headActions.drop 8).take 7) views arguments
  have oldRoots : ∀ slot, slot ∉ [27, 28, 29, 30, 33, 34, 35, 36] → after.roots slot = active.roots slot := by
    intro slot outside
    rw [rootsAfter, argumentScope.otherRoots slot (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto),
      otherV slot (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto)]
  refine ⟨fuel, budget, final, after, result, output, machine, countAfter.trans (argumentScope.count.trans countV),
    frameAfter.trans (argumentScope.frame.trans frameV), valueAfter, tupleAfter, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, native, emptyAfter, ?_, oldRoots, ?_, ?_⟩
  · have old : aa.state 1 = .shared (encodeWord (.Pair lh lt)) :=
      (first15.observed_local_same (index := 1) h.native.valid h.native.callersValid h.native.wellFormed
        (by intro offset bound; change offset < 15 at bound; interval_cases offset <;> decide +kernel)
        (by decide +kernel) (by decide +kernel)).trans scope.inputs.left
    rw [statesAfter]
    simp only [headMasks, Partial.Locals.set, show (1 : Nat) ≠ 33 by decide, show (1 : Nat) ≠ 36 by decide,
      show (1 : Nat) ≠ 35 by decide, show (1 : Nat) ≠ 34 by decide, ite_false]
    exact (Activation.forgetRefs_observed aa (headCode 15) 1 (by decide +kernel)).trans old
  · have old : aa.state 2 = .shared (encodeWord (.Pair rh rt)) :=
      (first15.observed_local_same (index := 2) h.native.valid h.native.callersValid h.native.wellFormed
        (by intro offset bound; change offset < 15 at bound; interval_cases offset <;> decide +kernel)
        (by decide +kernel) (by decide +kernel)).trans scope.inputs.right
    rw [statesAfter]
    simp only [headMasks, Partial.Locals.set, show (2 : Nat) ≠ 33 by decide, show (2 : Nat) ≠ 36 by decide,
      show (2 : Nat) ≠ 35 by decide, show (2 : Nat) ≠ 34 by decide, ite_false]
    exact (Activation.forgetRefs_observed aa (headCode 15) 2 (by decide +kernel)).trans old
  · rw [statesAfter]
    simp only [headMasks, Partial.Locals.set, show (3 : Nat) ≠ 33 by decide, show (3 : Nat) ≠ 36 by decide,
      show (3 : Nat) ≠ 35 by decide, show (3 : Nat) ≠ 34 by decide, ite_false]
    exact LoanEnding.forget_empty _ _ argumentScope.tableEmpty
  · have old : aa.state 0 = .empty :=
      (first15.closed_local_same (index := 0) h.native.valid h.native.callersValid h.native.wellFormed
        (by rw [scope.returnEmpty]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans scope.returnEmpty
    rw [statesAfter]
    simp only [headMasks, Partial.Locals.set, show (0 : Nat) ≠ 33 by decide, show (0 : Nat) ≠ 36 by decide,
      show (0 : Nat) ≠ 35 by decide, show (0 : Nat) ≠ 34 by decide, ite_false]
    exact LoanEnding.forget_empty _ _ old
  · have old := (head_argument_fields_same arguments mv.native.valid mv.native.callersValid mv.native.wellFormed 27 (by simp)).trans leftV
    rw [statesAfter]
    simp only [headMasks, Partial.Locals.set, show (27 : Nat) ≠ 33 by decide, show (27 : Nat) ≠ 36 by decide,
      show (27 : Nat) ≠ 35 by decide, show (27 : Nat) ≠ 34 by decide, ite_false]
    exact (Activation.forgetRefs_observed aa (headCode 15) 27 (by decide +kernel)).trans old
  · have old := (head_argument_fields_same arguments mv.native.valid mv.native.callersValid mv.native.wellFormed 28 (by simp)).trans leftTailV
    rw [statesAfter]
    simp only [headMasks, Partial.Locals.set, show (28 : Nat) ≠ 33 by decide, show (28 : Nat) ≠ 36 by decide,
      show (28 : Nat) ≠ 35 by decide, show (28 : Nat) ≠ 34 by decide, ite_false]
    exact (Activation.forgetRefs_observed aa (headCode 15) 28 (by decide +kernel)).trans old
  · have old := (head_argument_fields_same arguments mv.native.valid mv.native.callersValid mv.native.wellFormed 29 (by simp)).trans rightV
    rw [statesAfter]
    simp only [headMasks, Partial.Locals.set, show (29 : Nat) ≠ 33 by decide, show (29 : Nat) ≠ 36 by decide,
      show (29 : Nat) ≠ 35 by decide, show (29 : Nat) ≠ 34 by decide, ite_false]
    exact (Activation.forgetRefs_observed aa (headCode 15) 29 (by decide +kernel)).trans old
  · have old := (head_argument_fields_same arguments mv.native.valid mv.native.callersValid mv.native.wellFormed 30 (by simp)).trans rightTailV
    rw [statesAfter]
    simp only [headMasks, Partial.Locals.set, show (30 : Nat) ≠ 33 by decide, show (30 : Nat) ≠ 36 by decide,
      show (30 : Nat) ≠ 35 by decide, show (30 : Nat) ≠ 34 by decide, ite_false]
    exact (Activation.forgetRefs_observed aa (headCode 15) 30 (by decide +kernel)).trans old
  · intro slot member
    rw [rootsAfter]
    by_cases new : slot ∈ [33, 34, 35, 36]
    · exact argumentScope.bound slot new
    · rw [argumentScope.otherRoots slot new]
      apply liveV slot
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at member new ⊢; tauto
  · intro slot binding root raw read
    have untouched : slot ∉ [27, 28, 29, 30, 33, 34, 35, 36] := by
      intro member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rw [scope.otherRoots _ (by decide), unbound _ (by decide)] at root <;> cases root
    have rootV : av.roots slot = some binding := by
      rw [otherV slot (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at untouched ⊢; tauto)]; exact root
    have rootA : aa.roots slot = some binding := by
      rw [argumentScope.otherRoots slot (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at untouched ⊢; tauto)]; exact rootV
    exact memoryAfter slot binding (by intro same; subst slot; simp at untouched) rootA raw
      (memoryA slot binding rootV raw (memoryV slot binding root raw read))
  · intro largerFuel largerBudget fuelBound budgetBound
    have run := (callRun largerFuel largerBudget fuelBound budgetBound).2
    exact Calling.Prefix.append (suffix := headCode 16) (rest := [.call .evaluate headArgs 33])
      (first15.noncall_callee _ (by decide +kernel)) run

theorem head_request_smaller (lh lt rh rt : BalancedWord) :
    (OrderedSolver.toDyck lh).semilength + (OrderedSolver.toDyck rh).semilength <
      (OrderedSolver.toDyck (.Pair lh lt)).semilength + (OrderedSolver.toDyck (.Pair rh rt)).semilength := by
  simp only [OrderedSolver.toDyck, DyckWord.semilength_add, DyckWord.semilength_nest]
  omega

end SubtreeProofs.Rust.SourceEval.Evaluator
