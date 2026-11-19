module

public import SubtreeProofs.Rust.SourcePairMatchedWord
public import SubtreeProofs.Rust.SourceAggregateOwnerProvenance

/-! The actual matched pair aggregate retains the bounded owners of both Boxes
through physical retirement of their moved-out source storage. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_matched_word_complete_fresh {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) {heads tails : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : MatchedBoxesScope heads tails table total world active)
    (headAbove : LocalOwnersAbove before.memory.length world active 66)
    (tailAbove : LocalOwnersAbove before.memory.length world active 68) :
    ∃ final after,
      Calling.Prefix callee callers (matchedCode 23) ((matchedActions.drop 18).take 5) world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      MatchedWordScope heads tails table total final after ∧ after.roots = (active.roots.set 68 none).set 66 none ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      LocalOwnersAbove before.memory.length final after 65 ∧
      (∀ slot binding, slot ≠ 65 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  obtain ⟨final, after, steps, machine, finalScope, rootsAfter, countAfter, frameAfter, memoryAfter⟩ :=
    pair_matched_word_complete h callee scope
  have fresh := steps.aggregate_two_owner_provenance h.native.valid h.native.callersValid h.native.wellFormed
    headAbove tailAbove (by decide +kernel) (by decide +kernel)
  exact ⟨final, after, steps, machine, finalScope, rootsAfter, countAfter, frameAfter, fresh, memoryAfter⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
