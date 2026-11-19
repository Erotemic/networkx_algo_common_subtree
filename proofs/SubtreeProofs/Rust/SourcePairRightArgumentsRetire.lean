module

public import SubtreeProofs.Rust.SourcePairRightCallOriginal
public import SubtreeProofs.Rust.SourceOriginalRetirement

/-! Retire the three actual moved right-call arguments, preserving the native
recursive output and the already ended intermediate word-view mask. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def rightArgumentRetired (roots : Roots) : Roots := ((roots.set 94 none).set 92 none).set 91 none

theorem pair_right_arguments_retire_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) (bound : ∀ slot ∈ [91, 92, 94], ∃ binding, active.roots slot = some binding)
    (empty : ∀ slot ∈ [91, 93, 92, 94], active.state slot = .empty)
    {result : Option CommonEmbedding} {table : MemoTable} (output : active.state 90 = Slot.ofValue (encodeOutput result table)) :
    ∃ final after,
      Calling.Prefix callee callers (rightCode 28) ((rightActions.drop 25).take 3) world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.roots = rightArgumentRetired active.roots ∧ after.count = active.count ∧ final.memory = world.memory ∧
      after.state 90 = Slot.ofValue (encodeOutput result table) ∧ after.state 93 = .empty := by
  obtain ⟨root94, bound94⟩ := bound 94 (by simp)
  obtain ⟨root92, bound92⟩ := bound 92 (by simp)
  obtain ⟨root91, bound91⟩ := bound 91 (by simp)
  have plan : RetirementPlan active.roots ((rightActions.drop 25).take 3) (rightArgumentRetired active.roots) :=
    .dead bound94 (.dead (binding := root92) (by simpa [Roots.set] using bound92)
      (.dead (binding := root91) (by simpa [Roots.set] using bound91) (.nil _)))
  have zero : ZeroRetirement ((rightActions.drop 25).take 3) active.state := by
    intro slot member
    have selected : slot ∈ [91, 93, 92, 94] := by
      simp [rightActions] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      tauto
    rw [empty slot selected]; simp only [Slot.dropWork]
  obtain ⟨final, after, steps, machine, roots, count, memory⟩ := plan.complete_original callee (rightCode 28) h rfl zero
  refine ⟨final, after, steps, machine, roots, count, memory, ?_, ?_⟩
  · exact (steps.closed_local_same_calls (index := 90) (by rw [output]; exact ofValue_typed (encodeOutput_typed result table))
      (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (by decide +kernel)).trans output
  · exact (steps.unshared_local_same_calls (index := 93) (by rw [empty 93 (by simp)]; simp) (by decide +kernel)).trans (empty 93 (by simp))

end SubtreeProofs.Rust.SourceEval.Evaluator
