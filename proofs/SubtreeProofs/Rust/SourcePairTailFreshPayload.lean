module

public import SubtreeProofs.Rust.SourcePairHeadTailFreshEntry
public import SubtreeProofs.Rust.SourcePairScoreProgram

/-! The real successful-tail payload prefix yields independently bounded head
and tail witnesses for later checked score work and matched-word assembly. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem score_tail_payload_complete_fresh {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active) (callee : Derived.Callees)
    {lh lt rh rt : BalancedWord} {heads tails : CommonEmbedding} {table : MemoTable}
    (scope : PairTailScope initial lh lt rh rt heads (some tails) table world active)
    (headsAbove : LocalOwnersAbove before.memory.length world active 37)
    (tailsAbove : LocalOwnersAbove before.memory.length world active 41)
    (count : 49 ≤ active.count) (unbound48 : active.roots 48 = none) :
    ∃ final after,
      Calling.Prefix callee callers (scoreCode 6) (scoreActions.take 6) world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      after.state 41 = headPayloadHole ∧ after.state 47 = Slot.ofValue (encodeResult tails) ∧
      after.state 37 = Slot.ofValue (encodeResult heads) ∧
      after.state 42 = Slot.ofValue (encodeTable table) ∧
      after.state 28 = .shared (.boxed (encodeWord lt)) ∧ after.state 30 = .shared (.boxed (encodeWord rt)) ∧
      LocalOwnersAbove before.memory.length final after 37 ∧ LocalOwnersAbove before.memory.length final after 47 ∧
      (∀ slot binding, slot ≠ 47 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  obtain ⟨final, after, steps, machine, rootsAfter, countAfter, frameAfter, hole, tailsAfter, headsAfter, tableAfter, leftAfter, rightAfter, kept⟩ :=
    score_tail_payload_complete h callee scope count unbound48
  have tailFresh := optional_payload_owner_provenance h.native.valid h.native.callersValid h.native.wellFormed
    (by decide) (by decide) tailsAbove steps
  have headFresh := steps.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by decide +kernel))
    h.native.valid h.native.callersValid h.native.wellFormed headsAbove
  exact ⟨final, after, steps, machine, rootsAfter, countAfter, frameAfter, hole, tailsAfter, headsAfter,
    tableAfter, leftAfter, rightAfter, headFresh, tailFresh, kept⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
