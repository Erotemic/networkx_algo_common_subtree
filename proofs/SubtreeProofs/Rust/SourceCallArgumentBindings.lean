module

public import SubtreeProofs.Rust.SourceRawMaskPreservation
public import SubtreeProofs.Rust.SourceInlineMovePermissions

/-! Successful actual local-move arguments require real bound stack roots.
The parent root map survives the call even after those masks move out. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem operands_move_local_bound {world : World} {roots : Roots} {guarded : List Nat} {state after : State}
    {args : List Operand} {packets : List ValueCell} {slot : Nat}
    (run : Addressed.operands world roots guarded state args = some (packets, after))
    (member : Operand.move (.local slot) ∈ args) : ∃ binding, roots slot = some binding := by
  induction args generalizing state packets with
  | nil => cases member
  | cons first rest ih =>
    simp only [Addressed.operands, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨packet, middle⟩, firstRun, ⟨more, ending⟩, tailRun, same⟩ := run
    cases same
    rcases List.mem_cons.mp member with same | later
    · subst first
      obtain ⟨pointer, _, located, _⟩ := operand_move_iff.mp firstRun
      obtain ⟨binding, root, _⟩ := locate_inline_root (place := .local slot) trivial located
      exact ⟨binding, root⟩
    · exact ih tailRun later

namespace Derived

theorem call_move_local_bound {callee : Callees} {world final : World} {active after : Activation} {callers : List Activation}
    {function : Function} {args : List Operand} {destination slot : Nat} {cost : Cost}
    (run : Derived.call callee world active callers function args destination = some (final, after, cost))
    (member : Operand.move (.local slot) ∈ args) : ∃ binding, after.roots slot = some binding := by
  simp only [Derived.call, bind, Option.bind_eq_some_iff] at run
  obtain ⟨current, scan, suspended, callerScan, ⟨packets, masks⟩, arguments, remainder, remaining, binding, root,
    ⟨returned, packet, inner⟩, called, ⟨ending, state⟩, stored, run⟩ := run
  cases run
  exact operands_move_local_bound arguments member

end Derived
end SubtreeProofs.Rust.SourceEval.Addressed
