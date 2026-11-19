module

public import SubtreeProofs.Rust.SourcePairTailUnpack
import Mathlib.Tactic.IntervalCases

/-! The complete tail prefix reaches its native result switch with the held
head embedding, original query loans and fresh tail payload storage. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

structure PairTailScope (initial : Activation) (lh lt rh rt : BalancedWord) (heads : CommonEmbedding)
    (result : Option CommonEmbedding) (table : MemoTable) (world : World) (active : Activation) : Prop where
  count : active.count = initial.count
  frame : active.frame = initial.frame
  left : active.state 1 = .shared (encodeWord (.Pair lh lt))
  right : active.state 2 = .shared (encodeWord (.Pair rh rt))
  tuple : active.state 13 = queryTuple (.Pair lh lt) (.Pair rh rt)
  leftHead : active.state 27 = .shared (.boxed (encodeWord lh))
  leftTail : active.state 28 = .shared (.boxed (encodeWord lt))
  rightHead : active.state 29 = .shared (.boxed (encodeWord rh))
  rightTail : active.state 30 = .shared (.boxed (encodeWord rt))
  headHole : active.state 31 = headPayloadHole
  headTableEmpty : active.state 32 = .empty
  heads : active.state 37 = Slot.ofValue (encodeResult heads)
  result : active.state 41 = Slot.ofValue (encodeOption result)
  table : active.state 42 = Slot.ofValue (encodeTable table)
  payloadEmpty : active.state 47 = .empty
  payloadRoot : ∃ binding, active.roots 47 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])
  returnEmpty : active.state 0 = .empty
  returnRoot : ∃ binding, active.roots 0 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])
  tableEmpty : active.state 3 = .empty
  live : ∀ slot ∈ [41, 42, 47], ∃ binding, active.roots slot = some binding
  retired : ∀ slot ∈ [43, 44, 45, 46], active.roots slot = none
  otherRoots : ∀ slot, slot ∉ [41, 42, 43, 44, 45, 46, 47] → active.roots slot = initial.roots slot

theorem pair_tail_scope_complete {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {lh lt rh rt : BalancedWord} {heads : CommonEmbedding} {table : MemoTable}
    (scope : PairHeadScope initial lh lt rh rt (some heads) table world active)
    (support : ∀ slot, slot ∉ [0, 1, 2, 3, 13] → initial.roots slot = none)
    (count : 48 ≤ active.count) (childTotal : NativeTotal lt rt) :
    ∃ minimumFuel minimumBudget final after result output,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      PairTailScope active lh lt rh rt heads result output final after ∧
      memoized_common_embedding lt rt table = .ok (result, output) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers tailCases tailActions world active final after := by
  obtain ⟨fuel, budget, wc, ac, result, output, mc, countC, frameC, valueC, headsC, holeC, empty32C, tupleC,
    leftC, rightC, headLC, tailLC, headRC, tailRC, empty0C, empty3C, root0C, native, liveC, otherC, emptyC, stable⟩ :=
    pair_tail_prefix_complete h scope support (by omega) childTotal
  let callee := Helpers.callee 0 0
  obtain ⟨wr, ar, retirement, mr, rootsR, countR, memoryR, valueR⟩ :=
    pair_tail_retire_complete mc callee (fun slot member => liveC slot (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto)) emptyC valueC
  have unboundR : ∀ slot ∈ [41, 42, 47], ar.roots slot = none := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rw [rootsR, tailArgumentRetired] <;> simp only [Roots.set] <;>
      rw [otherC _ (by decide), scope.otherRoots _ (by decide)] <;> exact support _ (by decide)
  obtain ⟨final, after, unpack, machine, countAfter, frameAfter, resultAfter, tableAfter, payloadEmpty, payloadRoot,
    retired43, liveAfter, otherAfter, memoryAfter⟩ :=
    pair_tail_unpack_complete mr callee valueR (by rw [countR, countC]; exact count) unboundR
  have tail : Calling.Prefix callee callers tailCases (tailActions.drop 14) wc ac final after :=
    Calling.Prefix.append (suffix := tailCases) (rest := tailActions.drop 17) retirement unpack
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
  have emptySame : ∀ slot ∈ [0, 3, 32], after.state slot = ac.state slot := by
    intro slot member
    have empty : ac.state slot = .empty := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact empty0C
      · exact empty3C
      · exact empty32C
    exact tail.closed_local_same (index := slot) mc.native.valid mc.native.callersValid mc.native.wellFormed
      (by rw [empty]; exact .empty .u32) .u32 (by decide +kernel)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl <;> decide +kernel)
  obtain ⟨root0, bound0, raw0⟩ := root0C
  have root0R : ar.roots 0 = some root0 := by simpa [rootsR, tailArgumentRetired, Roots.set] using bound0
  have old0R : wr.memory[root0.address]? = some (.node .tuple 0 []) := by rw [memoryR]; exact raw0
  have finalScope : PairTailScope active lh lt rh rt heads result output final after := by
    refine ⟨countAfter.trans (countR.trans countC), frameAfter.trans ((retirement.frame_count mc.native.valid mc.native.callersValid mc.native.wellFormed (by decide +kernel)).1.trans frameC),
      (sharedSame 1 (by simp)).trans leftC, (sharedSame 2 (by simp)).trans rightC, ?_,
      (sharedSame 27 (by simp)).trans headLC, (sharedSame 28 (by simp)).trans tailLC,
      (sharedSame 29 (by simp)).trans headRC, (sharedSame 30 (by simp)).trans tailRC, ?_,
      (emptySame 32 (by simp)).trans empty32C, ?_, resultAfter, tableAfter, payloadEmpty, payloadRoot,
      (emptySame 0 (by simp)).trans empty0C, ⟨root0, ?_, memoryAfter 0 root0 root0R _ old0R⟩,
      (emptySame 3 (by simp)).trans empty3C, liveAfter, ?_, ?_⟩
    · exact (tail.unshared_local_same (index := 13) mc.native.valid mc.native.callersValid mc.native.wellFormed
        (by rw [tupleC]; intro value same; cases same) (by decide +kernel) (by decide +kernel)).trans tupleC
    · exact (tail.closed_local_same (index := 31) mc.native.valid mc.native.callersValid mc.native.wellFormed
        (by rw [holeC]; exact headPayloadHole_typed) (.adt .optional) (by decide +kernel) (by decide +kernel)).trans holeC
    · exact (tail.closed_local_same (index := 37) mc.native.valid mc.native.callersValid mc.native.wellFormed
        (by rw [headsC]; exact ofValue_typed (result_typed heads)) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans headsC
    · rw [otherAfter 0 (by decide)]; exact root0R
    · intro slot member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact retired43
      · rw [otherAfter 44 (by decide), rootsR]; simp [tailArgumentRetired, Roots.set]
      · rw [otherAfter 45 (by decide), rootsR]; simp [tailArgumentRetired, Roots.set]
      · rw [otherAfter 46 (by decide), rootsR]; simp [tailArgumentRetired, Roots.set]
    · intro slot outside
      rw [otherAfter slot (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto), rootsR]
      have different : slot ≠ 44 ∧ slot ≠ 45 ∧ slot ≠ 46 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto
      simp only [tailArgumentRetired, Roots.set, different.1, different.2.1, different.2.2, ite_false]
      exact otherC slot (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto)
  refine ⟨fuel, budget, final, after, result, output, machine, finalScope, native, ?_⟩
  intro largerFuel largerBudget fuelBound budgetBound
  exact Calling.Prefix.append (suffix := tailCases) (rest := tailActions.drop 14)
    (stable largerFuel largerBudget fuelBound budgetBound) (tail.noncall_callee _ (by decide +kernel))

end SubtreeProofs.Rust.SourceEval.Evaluator
