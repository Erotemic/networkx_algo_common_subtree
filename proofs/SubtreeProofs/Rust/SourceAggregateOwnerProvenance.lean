module

public import SubtreeProofs.Rust.SourceResultPrefixProvenance

/-! Actual aggregate assignment combines bounded source inventories and retains
that bound through primitive cleanup of the moved-out source storage. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem OperandSourcesAbove.two_moves {bound left right : Nat} {world : World} {active : Activation}
    (first : LocalOwnersAbove bound world active left) (second : LocalOwnersAbove bound world active right) :
    OperandSourcesAbove bound world active [.move (.local left), .move (.local right)] := by
  intro op member place same
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · cases same; exact first
  · cases same; exact second

namespace Calling

theorem Prefix.aggregate_two_owner_provenance {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {world final : World} {active after : Activation} {bound left right destination : Nat} {kind : Kind} {tag : Nat}
    {rest : List Action}
    (steps : Prefix callee callers suffix
      (.assign destination (.aggregate kind tag [.move (.local left), .move (.local right)]) :: rest) world active final after)
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (first : LocalOwnersAbove bound world active left) (second : LocalOwnersAbove bound world active right)
    (noncall : noCalls (rest.foldr Control.Tree.step .done) = true)
    (safe : rest.all (LocalPreservation.action destination) = true) : LocalOwnersAbove bound final after destination := by
  cases steps with
  | @cons _ middle _ _ current _ _ _ cost run tail =>
    let code := (Action.assign destination (.aggregate kind tag [.move (.local left), .move (.local right)]) :: rest).foldr Control.Tree.step suffix
    have valid := Activation.forgetRefs_valid ha code
    simp only [instruction, Derived.instruction, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨w, a⟩, acted, last⟩ := run
    cases last
    have checked := Derived.action_spec valid hc hw _ acted
    have fresh := Derived.assign_owner_provenance (rhs := .aggregate kind tag [.move (.local left), .move (.local right)]) valid
      (OperandSourcesAbove.two_moves (first.prepare_any code) (second.prepare_any code)) acted
    exact tail.owner_transfer (OwnerTransfer.kept noncall safe) checked.valid checked.callers checked.wellFormed fresh

end Calling
end SubtreeProofs.Rust.SourceEval.Addressed
