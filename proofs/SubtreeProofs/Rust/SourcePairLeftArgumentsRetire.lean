module

public import SubtreeProofs.Rust.SourcePairLeftCallOriginal
public import SubtreeProofs.Rust.SourceOriginalRetirement

/-! Retire the three actual moved left-call arguments, preserving the native
recursive output and the already ended intermediate word-view mask. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def leftArgumentRetired (roots : Roots) : Roots := ((roots.set 80 none).set 79 none).set 77 none

theorem pair_left_arguments_retire_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) (bound : ∀ slot ∈ [77, 79, 80], ∃ binding, active.roots slot = some binding)
    (empty : ∀ slot ∈ [77, 78, 79, 80], active.state slot = .empty)
    {result : Option CommonEmbedding} {table : MemoTable} (output : active.state 76 = Slot.ofValue (encodeOutput result table)) :
    ∃ final after,
      Calling.Prefix callee callers (matchedCode 52) ((matchedActions.drop 49).take 3) world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.roots = leftArgumentRetired active.roots ∧ after.count = active.count ∧ final.memory = world.memory ∧
      after.state 76 = Slot.ofValue (encodeOutput result table) ∧ after.state 78 = .empty := by
  obtain ⟨root80, bound80⟩ := bound 80 (by simp)
  obtain ⟨root79, bound79⟩ := bound 79 (by simp)
  obtain ⟨root77, bound77⟩ := bound 77 (by simp)
  have plan : RetirementPlan active.roots ((matchedActions.drop 49).take 3) (leftArgumentRetired active.roots) :=
    .dead bound80 (.dead (binding := root79) (by simpa [Roots.set] using bound79)
      (.dead (binding := root77) (by simpa [Roots.set] using bound77) (.nil _)))
  have zero : ZeroRetirement ((matchedActions.drop 49).take 3) active.state := by
    intro slot member
    have selected : slot ∈ [77, 78, 79, 80] := by
      simp [matchedActions] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      tauto
    rw [empty slot selected]; simp only [Slot.dropWork]
  obtain ⟨final, after, steps, machine, roots, count, memory⟩ := plan.complete_original callee (matchedCode 52) h rfl zero
  refine ⟨final, after, steps, machine, roots, count, memory, ?_, ?_⟩
  · exact (steps.closed_local_same_calls (index := 76) (by rw [output]; exact ofValue_typed (encodeOutput_typed result table))
      (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (by decide +kernel)).trans output
  · exact (steps.unshared_local_same_calls (index := 78) (by rw [empty 78 (by simp)]; simp) (by decide +kernel)).trans (empty 78 (by simp))

end SubtreeProofs.Rust.SourceEval.Evaluator
