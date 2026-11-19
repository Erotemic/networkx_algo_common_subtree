module

public import SubtreeProofs.Rust.SourcePairScoreScope
public import SubtreeProofs.Rust.SourceCheckedAddOwnerProvenance
public import SubtreeProofs.Rust.SourcePairTailFreshPayload

/-! Both independently bounded witnesses survive actual checked-score calls,
including numeric overflow, and their primitive cleanup instructions. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_score_scope_complete_fresh {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {lh lt rh rt : BalancedWord} {heads tails : CommonEmbedding} {table : MemoTable}
    (scope : PairTailScope initial lh lt rh rt heads (some tails) table world active)
    (headsAbove : LocalOwnersAbove before.memory.length world active 37)
    (tailsAbove : LocalOwnersAbove before.memory.length world active 41)
    (count : 55 ≤ active.count) (unbound : ∀ slot ∈ [48, 51, 52, 53, 54], active.roots slot = none) :
    ∃ minimumFuel minimumBudget final after,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      ScoreSumScope heads tails table final after ∧ after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [51, 52, 53, 54] → after.roots slot = active.roots slot) ∧
      (∀ slot binding, slot ≠ 47 → slot ≠ 52 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      Derived.scrutinee final after callers (.discriminant (.local 52)) =
        some (numberKey (checkedAdd32 heads.edges.val tails.edges.val), after) ∧
      LocalOwnersAbove before.memory.length final after 37 ∧ LocalOwnersAbove before.memory.length final after 47 ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers scoreCases scoreActions world active final after := by
  obtain ⟨fuel, budget, final, after, machine, finalScope, countAfter, frameAfter, rootsAfter, memoryAfter, inspection, stable⟩ :=
    pair_score_scope_complete h scope count unbound
  obtain ⟨wp, ap, payload, mp, _, countP, _, _, _, _, _, _, _, headsP, tailsP, _⟩ :=
    score_tail_payload_complete_fresh h (Recursive.original budget fuel) scope headsAbove tailsAbove (by omega) (unbound 48 (by simp))
  have whole : Calling.Prefix (Recursive.original budget fuel) callers scoreCases
      (scoreActions.take 6 ++ scoreActions.drop 6) world active final after := by
    simpa only [List.take_append_drop] using stable fuel budget (by rfl) (by rfl)
  obtain ⟨wa, aa, first, rest⟩ := whole.split
  have same := payload.unique first
  have am := mp
  have boundedP : 55 ≤ ap.count := by rw [countP]; exact count
  rw [same.1, same.2] at am headsP tailsP
  rw [same.2] at boundedP
  have headsAfter := rest.checkedAdd_keeps_owner_provenance am.native.valid am.native.callersValid am.native.wellFormed
    (by omega : 37 < aa.count) (by intro function args destination member; simp [scoreActions] at member; exact member.1) (by decide +kernel) headsP
  have tailsAfter := rest.checkedAdd_keeps_owner_provenance am.native.valid am.native.callersValid am.native.wellFormed
    (by omega : 47 < aa.count) (by intro function args destination member; simp [scoreActions] at member; exact member.1) (by decide +kernel) tailsP
  exact ⟨fuel, budget, final, after, machine, finalScope, countAfter, frameAfter, rootsAfter, memoryAfter,
    inspection, headsAfter, tailsAfter, stable⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
