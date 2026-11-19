module

public import SubtreeProofs.Rust.SourceResultOwnerProvenance
public import SubtreeProofs.Rust.SourcePrefixOwnerProvenance

/-! Construct witness-field provenance for an actual two-field tuple assignment.
The second field can transfer old owners; only the first moved source is bounded. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource Heap Partial Partial.Addressed Storage

theorem Prefix.aggregate_result_owner_provenance {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {world final : World} {active after : Activation} {bound first second destination : Nat}
    (steps : Prefix callee callers suffix
      [.assign destination (.aggregate .tuple 0 [.move (.local first), .move (.local second)])] world active final after)
    (ha : active.Valid world) (above : LocalOwnersAbove bound world active first) :
    LocalResultOwnersAbove bound final after destination := by
  cases steps with
  | cons run tail =>
    cases tail
    let code : Code := .step (.assign destination (.aggregate .tuple 0 [.move (.local first), .move (.local second)])) suffix
    have valid := Activation.forgetRefs_valid ha code
    simp only [instruction, Derived.instruction, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨w, a⟩, assigned, last⟩ := run
    cases last
    exact Derived.assign_result_owner_provenance valid
      (OperandSourcesAbove.single_move (above.prepare_any code) rfl) assigned

end SubtreeProofs.Rust.SourceEval.Addressed.Calling
