module

public import SubtreeProofs.Rust.SourcePairHeadPrefix
public import SubtreeProofs.Rust.SourceOriginalRetirement

/-! Retire all actual head-call argument roots after their moved masks clear.
The recursive output tuple is retained for native result/table extraction. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def headArgumentRetired (roots : Roots) : Roots := ((roots.set 36 none).set 35 none).set 34 none

theorem pair_head_retire_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [35, 34, 30, 29, 28, 27, 1, 2, 13] world active) (callee : Derived.Callees)
    (bound : ∀ slot ∈ [34, 35, 36], ∃ binding, active.roots slot = some binding)
    (empty : ∀ slot ∈ [34, 35, 36], active.state slot = .empty)
    {result : Option CommonEmbedding} {table : MemoTable} (output : active.state 33 = Slot.ofValue (encodeOutput result table)) :
    ∃ final after,
      Calling.Prefix callee callers (headCode 19) ((headActions.drop 16).take 3) world active final after ∧
      OriginalLoanMachine before callers previous external [35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.roots = headArgumentRetired active.roots ∧ after.count = active.count ∧ final.memory = world.memory ∧
      after.state 33 = Slot.ofValue (encodeOutput result table) := by
  obtain ⟨root36, bound36⟩ := bound 36 (by simp)
  obtain ⟨root35, bound35⟩ := bound 35 (by simp)
  obtain ⟨root34, bound34⟩ := bound 34 (by simp)
  have plan : RetirementPlan active.roots ((headActions.drop 16).take 3) (headArgumentRetired active.roots) :=
    .dead bound36 (.dead (binding := root35) (by simpa [Roots.set] using bound35)
      (.dead (binding := root34) (by simpa [Roots.set] using bound34) (.nil _)))
  have zero : ZeroRetirement ((headActions.drop 16).take 3) active.state := by
    intro slot member
    have selected : slot ∈ [34, 35, 36] := by simp [headActions] at member; simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto
    rw [empty slot selected]; simp only [Slot.dropWork]
  obtain ⟨final, after, steps, machine, roots, count, memory⟩ := plan.complete_original callee (headCode 19) h rfl zero
  refine ⟨final, after, steps, machine, roots, count, memory, ?_⟩
  exact (steps.closed_local_same (index := 33) h.native.valid h.native.callersValid h.native.wellFormed
    (by rw [output]; exact ofValue_typed (encodeOutput_typed result table))
    (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (by decide +kernel) (by decide +kernel)).trans output

end SubtreeProofs.Rust.SourceEval.Evaluator
