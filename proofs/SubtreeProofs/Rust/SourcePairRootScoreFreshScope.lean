module

public import SubtreeProofs.Rust.SourcePairRootScoreScope
public import SubtreeProofs.Rust.SourceCheckedAddOwnerProvenance

/-! Both independently bounded witnesses survive actual checked-score calls,
including numeric overflow, and their primitive cleanup instructions. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_root_score_scope_complete_fresh {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {heads tails : CommonEmbedding} {table : MemoTable}
    (scope : ScoreSumScope heads tails table world active) (subtotal : Aeneas.Std.U32)
    (success : Aeneas.Std.U32.checked_add heads.edges tails.edges = some subtotal)
    (headsAbove : LocalOwnersAbove before.memory.length world active 37)
    (tailsAbove : LocalOwnersAbove before.memory.length world active 47)
    (count : 61 ≤ active.count) (unbound : ∀ slot ∈ [55, 58, 59, 60], active.roots slot = none) :
    ∃ minimumFuel minimumBudget final after,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      RootScoreScope heads tails table subtotal final after ∧ after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [52, 58, 59, 60] → after.roots slot = active.roots slot) ∧
      (∀ slot binding, slot ∉ [51, 52, 59] → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      Derived.scrutinee final after callers (.discriminant (.local 59)) = some (numberKey (checkedAdd32 subtotal.val 1), after) ∧
      LocalOwnersAbove before.memory.length final after 37 ∧ LocalOwnersAbove before.memory.length final after 47 ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers rootScoreCases rootScoreActions world active final after := by
  obtain ⟨fuel, budget, final, after, machine, finalScope, countAfter, frameAfter, rootsAfter, memoryAfter, inspection, stable⟩ :=
    pair_root_score_scope_complete h scope subtotal success count unbound
  have steps := stable fuel budget (by rfl) (by rfl)
  have headsAfter := steps.checkedAdd_keeps_owner_provenance h.native.valid h.native.callersValid h.native.wellFormed
    (by omega : 37 < active.count) (by intro function args destination member; simp [rootScoreActions] at member; exact member.1) (by decide +kernel) headsAbove
  have tailsAfter := steps.checkedAdd_keeps_owner_provenance h.native.valid h.native.callersValid h.native.wellFormed
    (by omega : 47 < active.count) (by intro function args destination member; simp [rootScoreActions] at member; exact member.1) (by decide +kernel) tailsAbove
  exact ⟨fuel, budget, final, after, machine, finalScope, countAfter, frameAfter, rootsAfter, memoryAfter,
    inspection, headsAfter, tailsAfter, stable⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
