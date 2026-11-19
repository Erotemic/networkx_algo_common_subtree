module

public import SubtreeProofs.Rust.SourcePairHeadUnpack
import Mathlib.Tactic.IntervalCases

/-! All twenty-six head-prefix instructions reach the actual head-result
switch with native queries, boxed-child views, optional result, updated table,
fresh payload/return storage and complete original-loan ownership invariants. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

structure PairHeadScope (initial : Activation) (lh lt rh rt : BalancedWord) (result : Option CommonEmbedding) (table : MemoTable)
    (world : World) (active : Activation) : Prop where
  count : active.count = initial.count
  frame : active.frame = initial.frame
  left : active.state 1 = .shared (encodeWord (.Pair lh lt))
  right : active.state 2 = .shared (encodeWord (.Pair rh rt))
  tuple : active.state 13 = queryTuple (.Pair lh lt) (.Pair rh rt)
  leftHead : active.state 27 = .shared (.boxed (encodeWord lh))
  leftTail : active.state 28 = .shared (.boxed (encodeWord lt))
  rightHead : active.state 29 = .shared (.boxed (encodeWord rh))
  rightTail : active.state 30 = .shared (.boxed (encodeWord rt))
  result : active.state 31 = Slot.ofValue (encodeOption result)
  table : active.state 32 = Slot.ofValue (encodeTable table)
  payloadEmpty : active.state 37 = .empty
  payloadRoot : ∃ binding, active.roots 37 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])
  returnEmpty : active.state 0 = .empty
  returnRoot : ∃ binding, active.roots 0 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])
  tableEmpty : active.state 3 = .empty
  live : ∀ slot ∈ [27, 28, 29, 30, 31, 32, 37], ∃ binding, active.roots slot = some binding
  retired : ∀ slot ∈ [33, 34, 35, 36], active.roots slot = none
  otherRoots : ∀ slot, slot ∉ [27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37] → active.roots slot = initial.roots slot

theorem pair_head_scope_complete {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [1, 2, 13] world active)
    {lh lt rh rt : BalancedWord} {table : MemoTable} (scope : MissScope initial (.Pair lh lt) (.Pair rh rt) table world active)
    (unbound : ∀ slot, slot ∉ [1, 2, 3] → initial.roots slot = none) (count : 38 ≤ active.count)
    (childTotal : NativeTotal lh rh) :
    ∃ minimumFuel minimumBudget final after result output,
      OriginalLoanMachine before callers previous external [35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      PairHeadScope active lh lt rh rt result output final after ∧
      memoized_common_embedding lh rh table = .ok (result, output) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers headCases headActions world active final after := by
  obtain ⟨fuel, budget, wc, ac, result, output, mc, countC, frameC, valueC, tupleC, leftC, rightC, empty3C, empty0C,
    headLC, tailLC, headRC, tailRC, native, emptyC, liveC, otherC, memoryC, stable⟩ :=
    pair_head_prefix_complete h scope unbound (by omega) childTotal
  let callee := Helpers.callee 0 0
  obtain ⟨wr, ar, retirement, mr, rootsR, countR, memoryR, valueR⟩ :=
    pair_head_retire_complete mc callee (fun slot member => liveC slot (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto)) emptyC valueC
  have unboundR : ∀ slot ∈ [31, 32, 37], ar.roots slot = none := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rw [rootsR, headArgumentRetired] <;> simp only [Roots.set] <;>
      rw [otherC _ (by decide), scope.otherRoots _ (by decide)] <;> exact unbound _ (by decide)
  obtain ⟨final, after, unpack, machine, countAfter, frameAfter, resultAfter, tableAfter, payloadEmpty, payloadRoot,
    retired33, liveAfter, otherAfter, memoryAfter⟩ :=
    pair_head_unpack_complete mr callee valueR (by rw [countR, countC]; exact count) unboundR
  have tail : Calling.Prefix callee callers headCases (headActions.drop 16) wc ac final after :=
    Calling.Prefix.append (suffix := headCases) (rest := headActions.drop 19) retirement unpack
  have sharedSame : ∀ slot ∈ [1, 2, 27, 28, 29, 30], after.state slot = ac.state slot := by
    intro slot member
    apply tail.observed_local_same mc.native.valid mc.native.callersValid mc.native.wellFormed
    · intro offset bound
      change offset < 10 at bound
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> interval_cases offset <;> decide +kernel
    · decide +kernel
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have bound0C : ∀ binding, active.roots 0 = some binding → ac.roots 0 = some binding := by
    intro binding root; rw [otherC 0 (by decide)]; exact root
  obtain ⟨root0, bound0, raw0⟩ := scope.returnRoot
  have root0R : ar.roots 0 = some root0 := by simpa [rootsR, headArgumentRetired, Roots.set] using bound0C root0 bound0
  have old0R : wr.memory[root0.address]? = some (.node .tuple 0 []) := by rw [memoryR]; exact memoryC 0 root0 bound0 _ raw0
  have finalScope : PairHeadScope active lh lt rh rt result output final after := by
    refine ⟨countAfter.trans (countR.trans countC), frameAfter.trans ((retirement.frame_count mc.native.valid mc.native.callersValid mc.native.wellFormed (by decide +kernel)).1.trans frameC),
      (sharedSame 1 (by simp)).trans leftC, (sharedSame 2 (by simp)).trans rightC, ?_,
      (sharedSame 27 (by simp)).trans headLC, (sharedSame 28 (by simp)).trans tailLC,
      (sharedSame 29 (by simp)).trans headRC, (sharedSame 30 (by simp)).trans tailRC,
      resultAfter, tableAfter, payloadEmpty, payloadRoot, ?_, ⟨root0, ?_, memoryAfter 0 root0 root0R _ old0R⟩, ?_, ?_, ?_, ?_⟩
    · exact (tail.unshared_local_same (index := 13) mc.native.valid mc.native.callersValid mc.native.wellFormed
        (by rw [tupleC]; intro value same; cases same) (by decide +kernel) (by decide +kernel)).trans tupleC
    · exact (tail.closed_local_same (index := 0) mc.native.valid mc.native.callersValid mc.native.wellFormed
        (by rw [empty0C]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans empty0C
    · rw [otherAfter 0 (by decide)]; exact root0R
    · exact (tail.closed_local_same (index := 3) mc.native.valid mc.native.callersValid mc.native.wellFormed
        (by rw [empty3C]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans empty3C
    · intro slot member
      by_cases new : slot ∈ [31, 32, 37]
      · exact liveAfter slot new
      · have old : slot ∈ [27, 28, 29, 30] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at member new ⊢; tauto
        rw [otherAfter slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at old ⊢; rcases old with rfl | rfl | rfl | rfl <;> decide), rootsR, headArgumentRetired]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at old
        rcases old with rfl | rfl | rfl | rfl <;> simp only [Roots.set] <;> exact liveC _ (by simp)
    · intro slot member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact retired33
      · rw [otherAfter 34 (by decide), rootsR]; simp [headArgumentRetired, Roots.set]
      · rw [otherAfter 35 (by decide), rootsR]; simp [headArgumentRetired, Roots.set]
      · rw [otherAfter 36 (by decide), rootsR]; simp [headArgumentRetired, Roots.set]
    · intro slot outside
      rw [otherAfter slot (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto), rootsR]
      have different : slot ≠ 34 ∧ slot ≠ 35 ∧ slot ≠ 36 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto
      simp only [headArgumentRetired, Roots.set, different.1, different.2.1, different.2.2, ite_false]
      exact otherC slot (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto)
  refine ⟨fuel, budget, final, after, result, output, machine, finalScope, native, ?_⟩
  intro largerFuel largerBudget fuelBound budgetBound
  exact Calling.Prefix.append (suffix := headCases) (rest := headActions.drop 16)
    (stable largerFuel largerBudget fuelBound budgetBound) (tail.noncall_callee _ (by decide +kernel))

end SubtreeProofs.Rust.SourceEval.Evaluator
