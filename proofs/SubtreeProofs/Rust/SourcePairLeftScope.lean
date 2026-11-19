module

public import SubtreeProofs.Rust.SourcePairLeftUnpack

/-! The left contraction prefix reaches its actual optional-result switch:
original/fresh argument cleanup, native output extraction, ended-view storage
retirement and fresh payload opening are constructed from the actual source. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

structure PairLeftScope (lh lt rh rt : BalancedWord) (heads tails : CommonEmbedding) (total : Aeneas.Std.U32)
    (result : Option CommonEmbedding) (table : MemoTable) (world : World) (active : Activation) : Prop where
  queries : PairQueryScope lh lt rh rt active
  matched : MatchedCandidateScope heads tails total active
  wordValue : active.state 71 = Slot.ofValue (encodeWord (OrderedSolver.appendWord lh lt))
  resultValue : active.state 74 = Slot.ofValue (encodeOption result)
  tableValue : active.state 75 = Slot.ofValue (encodeTable table)
  oldTableEmpty : active.state 42 = .empty
  payloadEmpty : active.state 81 = .empty
  payloadRoot : ∃ binding, active.roots 81 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])
  live : ∀ slot ∈ [74, 75, 81], ∃ binding, active.roots slot = some binding
  retired : ∀ slot ∈ [76, 77, 78, 79, 80], active.roots slot = none

theorem left_result_scrutinee_source {state : State} {result : Option CommonEmbedding}
    (initialized : state 74 = Slot.ofValue (encodeOption result)) :
    SourceEval.scrutinee state (.discriminant (.local 74)) = some (lookupKey result, state) := by
  cases result <;> simp [SourceEval.scrutinee, splitPlace, initialized, encodeOption, Slot.ofValue, Slot.get, lookupKey]

theorem pair_left_scope_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat} {anchor : Resources}
    {lh lt rh rt : BalancedWord} {heads tails : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (h : AnchoredLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13]
      [77, 78] 71 (OrderedSolver.appendWord lh lt) anchor world active)
    (queries : PairQueryScope lh lt rh rt active) (candidate : MatchedScope heads tails table total active)
    (left : active.state 77 = .shared (encodeWord (OrderedSolver.appendWord lh lt)))
    (view78 : active.state 78 = .shared (encodeWord (OrderedSolver.appendWord lh lt)))
    (empty76 : active.state 76 = .empty)
    (root76 : ∃ binding, active.roots 76 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 []))
    (count : 82 ≤ active.count) (unbound : ∀ slot ∈ [74, 75, 79, 80, 81], active.roots slot = none)
    (childTotal : NativeTotal (OrderedSolver.appendWord lh lt) (.Pair rh rt)) :
    ∃ minimumFuel minimumBudget argumentWorld argumentActive callWorld callActive final after result output cost,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      PairLeftScope lh lt rh rt heads tails total result output final after ∧
      memoized_common_embedding (OrderedSolver.appendWord lh lt) (.Pair rh rt) table = .ok (result, output) ∧
      Derived.scrutinee final after callers (.discriminant (.local 74)) = some (lookupKey result, after) ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [74, 75, 76, 77, 78, 79, 80, 81] → after.roots slot = active.roots slot) ∧
      (∀ slot binding, slot ≠ 76 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 48) ((matchedActions.drop 44).take 4) world active argumentWorld argumentActive ∧
        Derived.call (Recursive.original budget fuel) argumentWorld (argumentActive.forgetRefs (matchedCode 48)) callers
          .evaluate leftContractionArgs 76 = some (callWorld, callActive, cost) ∧
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 49) [.call .evaluate leftContractionArgs 76] argumentWorld argumentActive callWorld callActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers matchedCases ((matchedActions.drop 49).take 11) callWorld callActive final after ∧
        Calling.Prefix (Recursive.original budget fuel) callers matchedCases ((matchedActions.drop 44).take 16) world active final after := by
  obtain ⟨fuel, budget, argumentWorld, argumentActive, callWorld, callActive, result, output, cost, mc, wordC, queriesC, candidateC,
    outputC, empty42C, moved, bound, native, countC, frameC, rootsC, memoryC, stable⟩ :=
    pair_left_call_original_complete h queries candidate left view78 empty76 root76 (by omega)
      (by intro slot member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl <;> exact unbound _ (by simp)) childTotal
  let callee := Helpers.callee 0 0
  obtain ⟨wr, ar, retirement, mr, rootsR, countR, memoryR, outputR, empty78R⟩ :=
    pair_left_arguments_retire_complete mc callee
      (by intro slot member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl <;> exact bound _ (by simp)) moved outputC
  have unboundR : ∀ slot ∈ [74, 75, 81], ar.roots slot = none := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rw [rootsR, leftArgumentRetired] <;> simp only [Roots.set] <;>
      rw [rootsC _ (by decide)] <;> exact unbound _ (by simp)
  obtain ⟨binding78, root78C⟩ := bound 78 (by simp)
  have root78R : ar.roots 78 = some binding78 := by simpa [rootsR, leftArgumentRetired, Roots.set] using root78C
  obtain ⟨final, after, unpack, machine, countAfter, frameAfter, resultValue, tableValue, payloadEmpty, payloadRoot,
    dead76, dead78, liveAfter, rootsAfter, memoryAfter, memoryExtendsAfter⟩ :=
    pair_left_unpack_complete mr callee outputR empty78R ⟨binding78, root78R⟩
      (by rw [countR, countC]; exact count) unboundR
  have cleanup : Calling.Prefix callee callers matchedCases ((matchedActions.drop 49).take 11) callWorld callActive final after :=
    Calling.Prefix.append (suffix := matchedCases) (rest := (matchedActions.drop 52).take 8) retirement unpack
  have queriesAfter : PairQueryScope lh lt rh rt after := by
    apply prefix_pair_queries_complete cleanup queriesC
    · intro slot member
      simp only [pairSharedQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    · intro slot member
      simp only [pairQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have candidateAfter := candidateC.through_prefix cleanup
    (by intro slot member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide +kernel)
    (by intro slot member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> simp [matchedActions, keepsRoot])
  have finalScope : PairLeftScope lh lt rh rt heads tails total result output final after := by
    refine ⟨queriesAfter, candidateAfter,
      (cleanup.closed_local_same_calls (index := 71) (by rw [wordC]; exact ofValue_typed (word_typed _)) (.adt .word) (by decide +kernel)).trans wordC,
      resultValue, tableValue,
      (cleanup.closed_local_same_calls (index := 42) (by rw [empty42C]; exact .empty .u32) .u32 (by decide +kernel)).trans empty42C,
      payloadEmpty, payloadRoot, liveAfter, ?_⟩
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact dead76
    · rw [rootsAfter 77 (by decide), rootsR]; simp [leftArgumentRetired, Roots.set]
    · exact dead78
    · rw [rootsAfter 79 (by decide), rootsR]; simp [leftArgumentRetired, Roots.set]
    · rw [rootsAfter 80 (by decide), rootsR]; simp [leftArgumentRetired, Roots.set]
  have inspection := Derived.scrutinee_complete machine.native.valid machine.native.callersValid _
    (left_result_scrutinee_source resultValue) (by intros; trivial)
  refine ⟨fuel, budget, argumentWorld, argumentActive, callWorld, callActive, final, after, result, output, cost,
    machine, finalScope, native, inspection, countAfter.trans (countR.trans countC), frameAfter.trans (retirement.shape.1.trans frameC), ?_, ?_, ?_⟩
  · intro slot outside
    have untouched : slot ∉ [74, 75, 76, 78, 81] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto
    have different : slot ≠ 77 ∧ slot ≠ 79 ∧ slot ≠ 80 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto
    rw [rootsAfter slot untouched, rootsR]
    simp only [leftArgumentRetired, Roots.set, different.1, different.2.1, different.2.2, ite_false]
    exact rootsC slot (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto)
  · intro slot binding different root raw memoryRead
    have outside : slot ∉ [79, 80] := by
      intro member
      have initial : slot ∈ [74, 75, 79, 80, 81] := List.mem_append_left [81] (List.mem_append_right [74, 75] member)
      rw [unbound slot initial] at root; cases root
    have rootC : callActive.roots slot = some binding := by rw [rootsC slot outside]; exact root
    have keptC := memoryC slot binding different root raw memoryRead
    have keptR : wr.memory[binding.address]? = some raw := by rw [memoryR]; exact keptC
    exact memoryExtendsAfter binding.address raw keptR
  · intro largerFuel largerBudget fuelBound budgetBound
    obtain ⟨arguments, callRun, callPrefix, first5⟩ := stable largerFuel largerBudget fuelBound budgetBound
    have cleanupRun := cleanup.noncall_callee (Recursive.original largerBudget largerFuel) (by decide +kernel)
    exact ⟨arguments, callRun, callPrefix, cleanupRun,
      Calling.Prefix.append (suffix := matchedCases) (rest := (matchedActions.drop 49).take 11) first5 cleanupRun⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
