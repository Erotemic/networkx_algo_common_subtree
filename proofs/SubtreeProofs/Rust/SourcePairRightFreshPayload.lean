module

public import SubtreeProofs.Rust.SourcePairRightPayload
public import SubtreeProofs.Rust.SourceOptionalPayloadOwnerProvenance

/-! The successful left witness transfers through actual scratch 82 to held
local 81, retaining the matched candidate and owned left query bounds. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_right_payload_complete_fresh {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) {lh lt rh rt : BalancedWord} {heads tails left : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : PairLeftScope lh lt rh rt heads tails total (some left) table world active)
    (leftAbove : LocalOwnersAbove before.memory.length world active 74)
    (candidateAbove : LocalOwnersAbove before.memory.length world active 64)
    (wordAbove : LocalOwnersAbove before.memory.length world active 71)
    (count : 83 ≤ active.count) (unbound : active.roots 82 = none) :
    ∃ final after,
      Calling.Prefix callee callers (rightCode 6) (rightActions.take 6) world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      RightPayloadScope lh lt rh rt heads tails left table total after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      LocalOwnersAbove before.memory.length final after 81 ∧
      LocalOwnersAbove before.memory.length final after 64 ∧ LocalOwnersAbove before.memory.length final after 71 ∧
      (∀ slot binding, slot ≠ 81 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  obtain ⟨final, after, steps, machine, scopeAfter, rootsAfter, countAfter, frameAfter, memoryAfter⟩ :=
    pair_right_payload_complete h callee scope count unbound
  have leftFresh := optional_payload_owner_provenance h.native.valid h.native.callersValid h.native.wellFormed
    (by decide) (by decide) leftAbove steps
  have candidateFresh := steps.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by decide +kernel))
    h.native.valid h.native.callersValid h.native.wellFormed candidateAbove
  have wordFresh := steps.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by decide +kernel))
    h.native.valid h.native.callersValid h.native.wellFormed wordAbove
  exact ⟨final, after, steps, machine, scopeAfter, rootsAfter, countAfter, frameAfter,
    leftFresh, candidateFresh, wordFresh, memoryAfter⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
