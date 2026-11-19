module

public import SubtreeProofs.Rust.SourceResultPrefixProvenance
public import SubtreeProofs.Rust.SourceOriginalOptionalPayload

/-! Bound transfer through the shared six-instruction optional payload pattern.
This generic source pattern is used by head, tail and both contractions. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem optional_payload_owner_provenance {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {world final : World} {active after : Activation} {bound source temporary destination : Nat}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (sourceTemp : source ≠ temporary) (tempDestination : temporary ≠ destination)
    (above : LocalOwnersAbove bound world active source)
    (steps : Calling.Prefix callee callers suffix (optionalPayloadActions source temporary destination) world active final after) :
    LocalOwnersAbove bound final after destination := by
  have plan : OwnerTransfer source (optionalPayloadActions source temporary destination) destination := by
    refine .keep rfl ?_ (.assign (fun _ _ _ h => OperandSourcesAbove.single_move h rfl)
      (.assign (fun _ _ _ h => OperandSourcesAbove.single_move h rfl) (.keep rfl ?_ (.keep rfl ?_ (.keep rfl rfl (.nil destination))))))
    · exact decide_eq_true sourceTemp
    · exact decide_eq_true (Ne.symm tempDestination)
    · exact decide_eq_true (Ne.symm tempDestination)
  exact steps.owner_transfer plan ha hc hw above


end SubtreeProofs.Rust.SourceEval.Evaluator
