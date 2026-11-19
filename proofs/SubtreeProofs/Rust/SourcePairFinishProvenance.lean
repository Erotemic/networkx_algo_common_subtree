module

public import SubtreeProofs.Rust.SourcePairFinishPayload

/-! All three candidate witnesses and both owned contraction words retain
their independently derived bounds at the actual finishCode 6 checkpoint. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_finish_payload_complete_provenance {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) {lh lt rh rt : BalancedWord} {heads tails left right : CommonEmbedding}
    {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : PairRightScope lh lt rh rt heads tails left total (some right) table world active)
    (above : LocalOwnersAbove before.memory.length world active 88)
    (heldAbove : ∀ slot ∈ [64, 71, 81, 85], LocalOwnersAbove before.memory.length world active slot)
    (count : 97 ≤ active.count) (unbound : active.roots 96 = none) :
    ∃ final after,
      Calling.Prefix callee callers (finishCode 6) (finishActions.take 6) world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      FinishPayloadScope lh lt rh rt heads tails left right table total after ∧
      LocalOwnersAbove before.memory.length final after 95 ∧
      (∀ slot ∈ [64, 71, 81, 85], LocalOwnersAbove before.memory.length final after slot) ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot binding, slot ≠ 95 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  obtain ⟨final, after, steps, machine, scopeAfter, fresh, rootsAfter, countAfter, frameAfter, memoryAfter⟩ :=
    pair_finish_payload_complete h callee scope above count unbound
  have heldFinal : ∀ slot ∈ [64, 71, 81, 85], LocalOwnersAbove before.memory.length final after slot := by
    intro slot member
    exact steps.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide +kernel))
      h.native.valid h.native.callersValid h.native.wellFormed (heldAbove slot member)
  exact ⟨final, after, steps, machine, scopeAfter, fresh, heldFinal, rootsAfter, countAfter, frameAfter, memoryAfter⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
