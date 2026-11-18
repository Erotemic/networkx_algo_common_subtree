module

public import SubtreeProofs.Rust.SourcePairTailPrefix
public import SubtreeProofs.Rust.SourceOriginalRetirement

/-! Retire all actual tail-call argument roots after their moved masks clear.
The recursive tail output tuple is retained for native result/table extraction. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def tailArgumentRetired (roots : Roots) : Roots := ((roots.set 46 none).set 45 none).set 44 none

theorem pair_tail_retire_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active) (callee : Derived.Callees)
    (bound : ∀ slot ∈ [44, 45, 46], ∃ binding, active.roots slot = some binding)
    (empty : ∀ slot ∈ [44, 45, 46], active.state slot = .empty)
    {result : Option CommonEmbedding} {table : MemoTable} (output : active.state 43 = Slot.ofValue (encodeOutput result table)) :
    ∃ final after,
      Calling.Prefix callee callers (tailCode 17) ((tailActions.drop 14).take 3) world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.roots = tailArgumentRetired active.roots ∧ after.count = active.count ∧ final.memory = world.memory ∧
      after.state 43 = Slot.ofValue (encodeOutput result table) := by
  obtain ⟨root46, bound46⟩ := bound 46 (by simp)
  obtain ⟨root45, bound45⟩ := bound 45 (by simp)
  obtain ⟨root44, bound44⟩ := bound 44 (by simp)
  have plan : RetirementPlan active.roots ((tailActions.drop 14).take 3) (tailArgumentRetired active.roots) :=
    .dead bound46 (.dead (binding := root45) (by simpa [Roots.set] using bound45)
      (.dead (binding := root44) (by simpa [Roots.set] using bound44) (.nil _)))
  have zero : ZeroRetirement ((tailActions.drop 14).take 3) active.state := by
    intro slot member
    have selected : slot ∈ [44, 45, 46] := by simp [tailActions] at member; simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto
    rw [empty slot selected]; simp only [Slot.dropWork]
  obtain ⟨final, after, steps, machine, roots, count, memory⟩ := plan.complete_original callee (tailCode 17) h rfl zero
  refine ⟨final, after, steps, machine, roots, count, memory, ?_⟩
  exact (steps.closed_local_same (index := 43) h.native.valid h.native.callersValid h.native.wellFormed
    (by rw [output]; exact ofValue_typed (encodeOutput_typed result table))
    (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (by decide +kernel) (by decide +kernel)).trans output

end SubtreeProofs.Rust.SourceEval.Evaluator
