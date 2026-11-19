module

public import SubtreeProofs.Rust.SourcePairRightCallPrefix
public import SubtreeProofs.Rust.SourceEndedReferenceMasks
public import SubtreeProofs.Rust.SourceOriginalLoanNarrowing
public import SubtreeProofs.Rust.SourceCallArgumentBindings

/-! Actual continuation preparation ends the intermediate word view before
recursion. Both fresh views and the moved original argument can then leave the
reference families without waiting for their physical stack retirement. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_right_call_original_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat} {anchor : Resources}
    {lh lt rh rt : BalancedWord} {heads tails leftWitness : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (h : AnchoredLoanMachine before callers previous external [91, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13]
      [92, 93] 85 (OrderedSolver.appendWord rh rt) anchor world active)
    (payload : RightPayloadScope lh lt rh rt heads tails leftWitness table total active)
    (leftView : active.state 91 = .shared (encodeWord (.Pair lh lt)))
    (rightView : active.state 92 = .shared (encodeWord (OrderedSolver.appendWord rh rt)))
    (view93 : active.state 93 = .shared (encodeWord (OrderedSolver.appendWord rh rt)))
    (empty90 : active.state 90 = .empty)
    (root90 : ∃ binding, active.roots 90 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 []))
    (count : 95 ≤ active.count) (unbound : active.roots 94 = none)
    (childTotal : NativeTotal (.Pair lh lt) (OrderedSolver.appendWord rh rt)) :
    ∃ minimumFuel minimumBudget argumentWorld argumentActive final after result output cost,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.state 85 = Slot.ofValue (encodeWord (OrderedSolver.appendWord rh rt)) ∧
      RightHeldScope lh lt rh rt heads tails leftWitness total after ∧
      after.state 90 = Slot.ofValue (encodeOutput result output) ∧ after.state 75 = .empty ∧
      (∀ slot ∈ [92, 93, 91, 94], after.state slot = .empty) ∧
      (∀ slot ∈ [92, 93, 91, 94], ∃ binding, after.roots slot = some binding) ∧
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
  obtain ⟨fuel, budget, argumentWorld, argumentActive, final, after, result, output, cost, machine, heldAfter,
    resultValue, tableMoved, moved, native, countAfter, frameAfter, rootsAfter, memoryAfter, stable⟩ :=
    pair_right_call_prefix_complete h payload leftView rightView empty90 root90 count unbound childTotal
  obtain ⟨arguments, callRun, called, whole⟩ := stable fuel budget (by rfl) (by rfl)
  have argument93 : argumentActive.state 93 = .empty :=
    arguments.ended_shared_local_empty_calls (index := 93) (by omega) view93 (by decide +kernel) (by decide +kernel)
  have ended93 : after.state 93 = .empty :=
    (called.unshared_local_same_calls (index := 93) (by rw [argument93]; simp) (by decide +kernel)).trans argument93
  have original := machine.to_original (by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨.u32, by rw [moved 92 (by simp)]; exact .empty _, .u32⟩
    · exact ⟨.u32, by rw [ended93]; exact .empty _, .u32⟩)
  have narrowed : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after :=
    original.narrow (fun _ member => List.mem_cons_of_mem 91 member) (by
      intro slot member outside
      rcases List.mem_cons.mp member with same | remaining
      · subst slot; exact ⟨.u32, by rw [moved 91 (by simp)]; exact .empty _, .u32⟩
      · exact False.elim (outside remaining))
  refine ⟨fuel, budget, argumentWorld, argumentActive, final, after, result, output, cost, narrowed, machine.value,
    heldAfter, resultValue, tableMoved, ?_, ?_, native, countAfter, frameAfter, rootsAfter, memoryAfter, stable⟩
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact moved 92 (by simp)
    · exact ended93
    · exact moved 91 (by simp)
    · exact moved 94 (by simp)
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact Derived.call_move_local_bound callRun (by simp [rightContractionArgs])
    · obtain ⟨binding, root⟩ := Activation.root_of_materialize h.native.valid
        (value := .reference (encodeWord (OrderedSolver.appendWord rh rt))) (by rw [view93]; simp only [Slot.materialize])
      exact ⟨binding, by rw [rootsAfter 93 (by decide)]; exact root⟩
    · exact Derived.call_move_local_bound callRun (by simp [rightContractionArgs])
    · exact Derived.call_move_local_bound callRun (by simp [rightContractionArgs])

end SubtreeProofs.Rust.SourceEval.Evaluator
