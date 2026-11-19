module

public import SubtreeProofs.Rust.SourcePairTailCall
import Mathlib.Tactic.IntervalCases

/-! Construct the first fourteen actual successful-head/tail instructions,
including the complete tail call. Head payload ownership, original queries,
child views, native tail output and stable machines are retained explicitly. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_tail_prefix_complete {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {lh lt rh rt : BalancedWord} {heads : CommonEmbedding} {table : MemoTable}
    (scope : PairHeadScope initial lh lt rh rt (some heads) table world active)
    (support : ∀ slot, slot ∉ [0, 1, 2, 3, 13] → initial.roots slot = none)
    (count : 47 ≤ active.count) (childTotal : NativeTotal lt rt) :
    ∃ minimumFuel minimumBudget final after result output,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      after.state 43 = Slot.ofValue (encodeOutput result output) ∧ after.state 37 = Slot.ofValue (encodeResult heads) ∧
      after.state 31 = headPayloadHole ∧ after.state 32 = .empty ∧ after.state 13 = queryTuple (.Pair lh lt) (.Pair rh rt) ∧
      after.state 1 = .shared (encodeWord (.Pair lh lt)) ∧ after.state 2 = .shared (encodeWord (.Pair rh rt)) ∧
      after.state 27 = .shared (.boxed (encodeWord lh)) ∧ after.state 28 = .shared (.boxed (encodeWord lt)) ∧
      after.state 29 = .shared (.boxed (encodeWord rh)) ∧ after.state 30 = .shared (.boxed (encodeWord rt)) ∧
      after.state 0 = .empty ∧ after.state 3 = .empty ∧
      (∃ root0, after.roots 0 = some root0 ∧ final.memory[root0.address]? = some (.node .tuple 0 [])) ∧
      memoized_common_embedding lt rt table = .ok (result, output) ∧
      (∀ slot ∈ [43, 44, 45, 46], ∃ binding, after.roots slot = some binding) ∧
      (∀ slot, slot ∉ [43, 44, 45, 46] → after.roots slot = active.roots slot) ∧
      (∀ slot ∈ [44, 45, 46], after.state slot = .empty) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers (tailCode 14) (tailActions.take 14) world active final after := by
  let callee := Helpers.callee 0 0
  have unbound : ∀ slot ∈ [38, 43, 44, 45, 46], active.roots slot = none := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> rw [scope.otherRoots _ (by decide)] <;> exact support _ (by decide)
  obtain ⟨wp, ap, payloadRun, mp, rootsP, countP, frameP, holeP, valueP, tableP, leftP, rightP, memoryP⟩ :=
    tail_head_payload_complete h callee scope (by omega) (unbound 38 (by simp))
  have tupleP : ap.state 13 = queryTuple (.Pair lh lt) (.Pair rh rt) :=
    (payloadRun.unshared_local_same (index := 13) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.tuple]; intro value same; cases same) (by decide +kernel) (by decide +kernel)).trans scope.tuple
  obtain ⟨wa, aa, arguments, ma, argumentScope, memoryA⟩ :=
    pair_tail_arguments_complete mp callee tupleP leftP rightP tableP (by rw [countP]; exact count)
      (by intro slot member; rw [rootsP]; exact unbound slot (List.mem_cons_of_mem _ member))
  have payloadA : aa.state 37 = Slot.ofValue (encodeResult heads) :=
    (arguments.closed_local_same (index := 37) mp.native.valid mp.native.callersValid mp.native.wellFormed
      (by rw [valueP]; exact ofValue_typed (result_typed heads)) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans valueP
  have holeA : aa.state 31 = headPayloadHole :=
    (arguments.closed_local_same (index := 31) mp.native.valid mp.native.callersValid mp.native.wellFormed
      (by rw [holeP]; exact headPayloadHole_typed) (.adt .optional) (by decide +kernel) (by decide +kernel)).trans holeP
  obtain ⟨fuel, budget, final, after, result, output, cost, machine, rootsAfter, countAfter, frameAfter, statesAfter, valueAfter, payloadAfter,
    holeAfter, tableAfter, tupleAfter, native, memoryAfter, callRun⟩ :=
    pair_tail_call_complete ma argumentScope payloadA holeA (by rw [argumentScope.count, countP]; exact count) childTotal
  have first13 : Calling.Prefix callee callers (tailCode 13) (tailActions.take 13) world active wa aa :=
    Calling.Prefix.append (suffix := tailCode 13) (rest := (tailActions.drop 6).take 7) payloadRun arguments
  have sharedSame : ∀ slot ∈ [1, 2, 27, 28, 29, 30], after.state slot = active.state slot := by
    intro slot member
    have old := first13.observed_local_same (index := slot) h.native.valid h.native.callersValid h.native.wellFormed
      (by intro offset bound
          change offset < 13 at bound
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> interval_cases offset <;> decide +kernel)
      (by decide +kernel)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
    have observed : (aa.forgetRefs (tailCode 13)).state slot = aa.state slot := by
      apply Activation.forgetRefs_observed
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    rw [statesAfter]
    have different : slot ≠ 43 ∧ slot ≠ 44 ∧ slot ≠ 45 ∧ slot ≠ 46 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [nativeCallMasks, Partial.Locals.set, different.1, different.2.1, different.2.2.1, different.2.2.2, ite_false] using observed.trans old
  have emptyBefore : ∀ slot ∈ [0, 3], aa.state slot = .empty := by
    intro slot member
    have initialEmpty : active.state slot = .empty := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl; exact scope.returnEmpty; exact scope.tableEmpty
    exact (first13.closed_local_same (index := slot) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [initialEmpty]; exact .empty .u32) .u32 (by decide +kernel)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> decide +kernel)).trans initialEmpty
  have emptyAfter : ∀ slot ∈ [0, 3], after.state slot = .empty := by
    intro slot member
    rw [statesAfter]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp only [nativeCallMasks, Partial.Locals.set] <;>
      exact LoanEnding.forget_empty _ _ (emptyBefore _ (by simp))
  have rootSame : ∀ slot, slot ∉ [43, 44, 45, 46] → after.roots slot = active.roots slot := by
    intro slot outside
    rw [rootsAfter, argumentScope.otherRoots slot outside, rootsP]
  obtain ⟨root0, bound0, raw0⟩ := scope.returnRoot
  have root0P : ap.roots 0 = some root0 := by rw [rootsP]; exact bound0
  have root0A : aa.roots 0 = some root0 := by rw [argumentScope.otherRoots 0 (by decide)]; exact root0P
  have raw0P := memoryP 0 root0 (by decide) bound0 _ raw0
  refine ⟨fuel, budget, final, after, result, output, machine, countAfter.trans (argumentScope.count.trans countP),
    frameAfter.trans (argumentScope.frame.trans frameP), valueAfter, payloadAfter, holeAfter, tableAfter, tupleAfter,
    (sharedSame 1 (by simp)).trans scope.left, (sharedSame 2 (by simp)).trans scope.right,
    (sharedSame 27 (by simp)).trans scope.leftHead, (sharedSame 28 (by simp)).trans scope.leftTail,
    (sharedSame 29 (by simp)).trans scope.rightHead, (sharedSame 30 (by simp)).trans scope.rightTail,
    emptyAfter 0 (by simp), emptyAfter 3 (by simp),
    ⟨root0, by rw [rootSame 0 (by decide)]; exact bound0, memoryAfter 0 root0 (by decide) root0A _ (memoryA 0 root0 root0P _ raw0P)⟩,
    native, ?_, rootSame, ?_, ?_⟩
  · intro slot member; rw [rootsAfter]; exact argumentScope.bound slot member
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp [statesAfter, nativeCallMasks, Partial.Locals.set]
  · intro largerFuel largerBudget fuelBound budgetBound
    exact Calling.Prefix.append (suffix := tailCode 14) (rest := [.call .evaluate (nativeCallArgs 44 45 46) 43])
      (first13.noncall_callee _ (by decide +kernel)) (callRun largerFuel largerBudget fuelBound budgetBound).2

theorem tail_request_smaller (lh lt rh rt : BalancedWord) :
    (OrderedSolver.toDyck lt).semilength + (OrderedSolver.toDyck rt).semilength <
      (OrderedSolver.toDyck (.Pair lh lt)).semilength + (OrderedSolver.toDyck (.Pair rh rt)).semilength := by
  simp only [OrderedSolver.toDyck, DyckWord.semilength_add, DyckWord.semilength_nest]
  omega

end SubtreeProofs.Rust.SourceEval.Evaluator
