module

public import SubtreeProofs.Rust.SourcePairLeftCallPrefix
public import SubtreeProofs.Rust.SourceEndedReferenceMasks
public import SubtreeProofs.Rust.SourceOriginalLoanNarrowing
public import SubtreeProofs.Rust.SourceCallArgumentBindings

/-! Actual continuation preparation ends the intermediate word view before
recursion. Both fresh views and the moved original argument can then leave the
reference families without waiting for their physical stack retirement. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_left_call_original_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat} {anchor : Resources}
    {lh lt rh rt : BalancedWord} {heads tails : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (h : AnchoredLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13]
      [77, 78] 71 (OrderedSolver.appendWord lh lt) anchor world active)
    (queries : PairQueryScope lh lt rh rt active) (candidate : MatchedScope heads tails table total active)
    (left : active.state 77 = .shared (encodeWord (OrderedSolver.appendWord lh lt)))
    (view78 : active.state 78 = .shared (encodeWord (OrderedSolver.appendWord lh lt)))
    (empty76 : active.state 76 = .empty)
    (root76 : ∃ binding, active.roots 76 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 []))
    (count : 81 ≤ active.count) (unbound : ∀ slot ∈ [79, 80], active.roots slot = none)
    (childTotal : NativeTotal (OrderedSolver.appendWord lh lt) (.Pair rh rt)) :
    ∃ minimumFuel minimumBudget argumentWorld argumentActive final after result output cost,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.state 71 = Slot.ofValue (encodeWord (OrderedSolver.appendWord lh lt)) ∧
      PairQueryScope lh lt rh rt after ∧ MatchedCandidateScope heads tails total after ∧
      after.state 76 = Slot.ofValue (encodeOutput result output) ∧ after.state 42 = .empty ∧
      (∀ slot ∈ [77, 78, 79, 80], after.state slot = .empty) ∧
      (∀ slot ∈ [77, 78, 79, 80], ∃ binding, after.roots slot = some binding) ∧
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
  obtain ⟨fuel, budget, argumentWorld, argumentActive, final, after, result, output, cost, machine, queriesAfter, candidateAfter,
    resultValue, tableMoved, moved, native, countAfter, frameAfter, rootsAfter, memoryAfter, stable⟩ :=
    pair_left_call_prefix_complete h queries candidate left empty76 root76 count unbound childTotal
  obtain ⟨arguments, callRun, called, whole⟩ := stable fuel budget (by rfl) (by rfl)
  have argument78 : argumentActive.state 78 = .empty :=
    arguments.ended_shared_local_empty_calls (index := 78) (by omega) view78 (by decide +kernel) (by decide +kernel)
  have ended78 : after.state 78 = .empty :=
    (called.unshared_local_same_calls (index := 78) (by rw [argument78]; simp) (by decide +kernel)).trans argument78
  have original := machine.to_original (by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨.u32, by rw [moved 77 (by simp)]; exact .empty _, .u32⟩
    · exact ⟨.u32, by rw [ended78]; exact .empty _, .u32⟩)
  have narrowed : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after :=
    original.narrow (fun _ member => List.mem_cons_of_mem 79 member) (by
      intro slot member outside
      rcases List.mem_cons.mp member with same | remaining
      · subst slot; exact ⟨.u32, by rw [moved 79 (by simp)]; exact .empty _, .u32⟩
      · exact False.elim (outside remaining))
  refine ⟨fuel, budget, argumentWorld, argumentActive, final, after, result, output, cost, narrowed, machine.value,
    queriesAfter, candidateAfter, resultValue, tableMoved, ?_, ?_, native, countAfter, frameAfter, rootsAfter, memoryAfter, stable⟩
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact moved 77 (by simp)
    · exact ended78
    · exact moved 79 (by simp)
    · exact moved 80 (by simp)
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact Derived.call_move_local_bound callRun (by simp [leftContractionArgs])
    · obtain ⟨binding, root⟩ := Activation.root_of_materialize h.native.valid
        (value := .reference (encodeWord (OrderedSolver.appendWord lh lt))) (by rw [view78]; simp only [Slot.materialize])
      exact ⟨binding, by rw [rootsAfter 78 (by decide)]; exact root⟩
    · exact Derived.call_move_local_bound callRun (by simp [leftContractionArgs])
    · exact Derived.call_move_local_bound callRun (by simp [leftContractionArgs])

end SubtreeProofs.Rust.SourceEval.Evaluator
