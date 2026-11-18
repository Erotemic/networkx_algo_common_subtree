module

public import SubtreeProofs.Rust.SourcePairMatchedEmbedding
public import SubtreeProofs.Rust.SourceAggregateOwnerProvenance

/-! The matched embedding combines the bounded native pair word with a scalar
score and retains the bound through all actual construction cleanup. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_matched_embedding_complete_fresh {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) {heads tails : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : MatchedWordScope heads tails table total world active) (wordAbove : LocalOwnersAbove before.memory.length world active 65) (count : 71 ≤ active.count) (unbound70 : active.roots 70 = none) :
    ∃ final after,
      Calling.Prefix callee callers (matchedCode 30) ((matchedActions.drop 23).take 7) world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      MatchedScope heads tails table total after ∧ after.roots = active.roots.set 65 none ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      LocalOwnersAbove before.memory.length final after 64 ∧
      (∀ slot binding, slot ≠ 64 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  obtain ⟨final, after, steps, machine, finalScope, rootsAfter, countAfter, frameAfter, memoryAfter⟩ :=
    pair_matched_embedding_complete h callee scope count unbound70
  obtain ⟨wp, ap, copied, mp, _, _, _, _, valueP, _⟩ :=
    original_number_copy_complete h callee (matchedCode 25) (source := 58) (destination := 70) (by decide) (by decide) (by decide)
      scope.totalValue (.local 58) rfl (number_local_read total.val) total.hmax (by omega) unbound70
  have wordP := copied.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by decide +kernel))
    h.native.valid h.native.callersValid h.native.wellFormed wordAbove
  have numberP : LocalOwnersAbove before.memory.length wp ap 70 :=
    LocalOwnersAbove.of_zero (by rw [valueP]; simp only [Slot.dropWork])
  have splitWhole : Calling.Prefix callee callers (matchedCode 30)
      (((matchedActions.drop 23).take 2) ++ ((matchedActions.drop 25).take 5)) world active final after := steps
  obtain ⟨wa, aa, actualFirst, rest⟩ := splitWhole.split
  have same := copied.unique actualFirst
  have am := mp
  rw [same.1, same.2] at am wordP numberP
  have fresh := rest.aggregate_two_owner_provenance am.native.valid am.native.callersValid am.native.wellFormed
    wordP numberP (by decide +kernel) (by decide +kernel)
  exact ⟨final, after, steps, machine, finalScope, rootsAfter, countAfter, frameAfter, fresh, memoryAfter⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
