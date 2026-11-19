module

public import SubtreeProofs.Rust.SourcePairRightUnpack

/-! The actual right contraction call and cleanup reach its native optional
switch while retaining both owned queries, the left witness and candidate. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

structure PairRightScope (lh lt rh rt : BalancedWord) (heads tails leftWitness : CommonEmbedding) (total : Aeneas.Std.U32)
    (result : Option CommonEmbedding) (table : MemoTable) (world : World) (active : Activation) : Prop where
  held : RightHeldScope lh lt rh rt heads tails leftWitness total active
  wordValue : active.state 85 = Slot.ofValue (encodeWord (OrderedSolver.appendWord rh rt))
  resultValue : active.state 88 = Slot.ofValue (encodeOption result)
  tableValue : active.state 89 = Slot.ofValue (encodeTable table)
  oldTableEmpty : active.state 75 = .empty
  payloadEmpty : active.state 95 = .empty
  payloadRoot : ∃ binding, active.roots 95 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])
  live : ∀ slot ∈ [88, 89, 95], ∃ binding, active.roots slot = some binding
  retired : ∀ slot ∈ [86, 87, 90, 91, 93, 92, 94], active.roots slot = none

theorem right_result_scrutinee_source {state : State} {result : Option CommonEmbedding}
    (initialized : state 88 = Slot.ofValue (encodeOption result)) :
    SourceEval.scrutinee state (.discriminant (.local 88)) = some (lookupKey result, state) := by
  cases result <;> simp [SourceEval.scrutinee, splitPlace, initialized, encodeOption, Slot.ofValue, Slot.get, lookupKey]

theorem pair_right_scope_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat} {anchor : Resources}
    {lh lt rh rt : BalancedWord} {heads tails leftWitness : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (h : AnchoredLoanMachine before callers previous external [91, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13]
      [92, 93] 85 (OrderedSolver.appendWord rh rt) anchor world active)
    (scope : RightConcatScope lh lt rh rt heads tails leftWitness table total active)
    (leftView : active.state 91 = .shared (encodeWord (.Pair lh lt)))
    (rightView : active.state 92 = .shared (encodeWord (OrderedSolver.appendWord rh rt)))
    (view93 : active.state 93 = .shared (encodeWord (OrderedSolver.appendWord rh rt)))
    (empty90 : active.state 90 = .empty)
    (root90 : ∃ binding, active.roots 90 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 []))
    (count : 96 ≤ active.count) (unbound : ∀ slot ∈ [88, 89, 94, 95], active.roots slot = none)
    (childTotal : NativeTotal (.Pair lh lt) (OrderedSolver.appendWord rh rt)) :
    ∃ minimumFuel minimumBudget argumentWorld argumentActive callWorld callActive final after result output cost,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      PairRightScope lh lt rh rt heads tails leftWitness total result output final after ∧
      memoized_common_embedding (.Pair lh lt) (OrderedSolver.appendWord rh rt) table = .ok (result, output) ∧
      Derived.scrutinee final after callers (.discriminant (.local 88)) = some (lookupKey result, after) ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [88, 89, 90, 91, 93, 92, 94, 95] → after.roots slot = active.roots slot) ∧
      (∀ slot binding, slot ≠ 90 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers (rightCode 24) ((rightActions.drop 22).take 2) world active argumentWorld argumentActive ∧
        Derived.call (Recursive.original budget fuel) argumentWorld (argumentActive.forgetRefs (rightCode 24)) callers
          .evaluate rightContractionArgs 90 = some (callWorld, callActive, cost) ∧
        Calling.Prefix (Recursive.original budget fuel) callers (rightCode 25) [.call .evaluate rightContractionArgs 90] argumentWorld argumentActive callWorld callActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers rightContractionCases ((rightActions.drop 25).take 11) callWorld callActive final after ∧
        Calling.Prefix (Recursive.original budget fuel) callers rightContractionCases ((rightActions.drop 22).take 14) world active final after := by
  obtain ⟨fuel, budget, argumentWorld, argumentActive, callWorld, callActive, result, output, cost, mc, wordC, heldC,
    outputC, empty75C, moved, bound, native, countC, frameC, rootsC, memoryC, stable⟩ :=
    pair_right_call_original_complete h scope.payload leftView rightView view93 empty90 root90 (by omega)
      (unbound 94 (by simp)) childTotal
  let callee := Helpers.callee 0 0
  obtain ⟨wr, ar, retirement, mr, rootsR, countR, memoryR, outputR, empty93R⟩ :=
    pair_right_arguments_retire_complete mc callee
      (by intro slot member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl <;> exact bound _ (by simp))
      (by intro slot member; exact moved slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto)) outputC
  have unboundR : ∀ slot ∈ [88, 89, 95], ar.roots slot = none := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rw [rootsR, rightArgumentRetired] <;> simp only [Roots.set] <;>
      rw [rootsC _ (by decide)] <;> exact unbound _ (by simp)
  obtain ⟨binding93, root93C⟩ := bound 93 (by simp)
  have root93R : ar.roots 93 = some binding93 := by simpa [rootsR, rightArgumentRetired, Roots.set] using root93C
  obtain ⟨final, after, unpack, machine, countAfter, frameAfter, resultValue, tableValue, payloadEmpty, payloadRoot,
    dead90, dead93, liveAfter, rootsAfter, memoryAfter, memoryExtendsAfter⟩ :=
    pair_right_unpack_complete mr callee outputR empty93R ⟨binding93, root93R⟩
      (by rw [countR, countC]; exact count) unboundR
  have cleanup : Calling.Prefix callee callers rightContractionCases ((rightActions.drop 25).take 11) callWorld callActive final after :=
    Calling.Prefix.append (suffix := rightContractionCases) (rest := (rightActions.drop 28).take 8) retirement unpack
  have heldAfter := heldC.through_prefix cleanup
    (by intro slot member
        simp only [pairSharedQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
    (by intro slot member
        simp only [pairQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
    (by intro slot member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
    (by intro slot member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [rightActions, keepsRoot])
  have finalScope : PairRightScope lh lt rh rt heads tails leftWitness total result output final after := by
    refine ⟨heldAfter,
      (cleanup.closed_local_same_calls (index := 85) (by rw [wordC]; exact ofValue_typed (word_typed _)) (.adt .word) (by decide +kernel)).trans wordC,
      resultValue, tableValue,
      (cleanup.closed_local_same_calls (index := 75) (by rw [empty75C]; exact .empty .u32) .u32 (by decide +kernel)).trans empty75C,
      payloadEmpty, payloadRoot, liveAfter, ?_⟩
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [rootsAfter 86 (by decide), rootsR, rightArgumentRetired]
      simpa [Roots.set, rootsC 86 (by decide)] using scope.retired 86 (by simp)
    · rw [rootsAfter 87 (by decide), rootsR, rightArgumentRetired]
      simpa [Roots.set, rootsC 87 (by decide)] using scope.retired 87 (by simp)
    · exact dead90
    · rw [rootsAfter 91 (by decide), rootsR]; simp [rightArgumentRetired, Roots.set]
    · exact dead93
    · rw [rootsAfter 92 (by decide), rootsR]; simp [rightArgumentRetired, Roots.set]
    · rw [rootsAfter 94 (by decide), rootsR]; simp [rightArgumentRetired, Roots.set]
  have inspection := Derived.scrutinee_complete machine.native.valid machine.native.callersValid _
    (right_result_scrutinee_source resultValue) (by intros; trivial)
  refine ⟨fuel, budget, argumentWorld, argumentActive, callWorld, callActive, final, after, result, output, cost,
    machine, finalScope, native, inspection, countAfter.trans (countR.trans countC), frameAfter.trans (retirement.shape.1.trans frameC), ?_, ?_, ?_⟩
  · intro slot outside
    have untouched : slot ∉ [88, 89, 90, 93, 95] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto
    have different : slot ≠ 91 ∧ slot ≠ 92 ∧ slot ≠ 94 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto
    rw [rootsAfter slot untouched, rootsR]
    simp only [rightArgumentRetired, Roots.set, different.1, different.2.1, different.2.2, ite_false]
    exact rootsC slot (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto)
  · intro slot binding different root raw memoryRead
    have outside : slot ≠ 94 := by
      intro same; subst slot; rw [unbound 94 (by simp)] at root; cases root
    have keptC := memoryC slot binding different root raw memoryRead
    have keptR : wr.memory[binding.address]? = some raw := by rw [memoryR]; exact keptC
    exact memoryExtendsAfter binding.address raw keptR
  · intro largerFuel largerBudget fuelBound budgetBound
    obtain ⟨arguments, callRun, callPrefix, first3⟩ := stable largerFuel largerBudget fuelBound budgetBound
    have cleanupRun := cleanup.noncall_callee (Recursive.original largerBudget largerFuel) (by decide +kernel)
    exact ⟨arguments, callRun, callPrefix, cleanupRun,
      Calling.Prefix.append (suffix := rightContractionCases) (rest := (rightActions.drop 25).take 11) first3 cleanupRun⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
