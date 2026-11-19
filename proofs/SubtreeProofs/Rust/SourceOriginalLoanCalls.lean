module

public import SubtreeProofs.Rust.SourceOriginalLoanMachine
public import SubtreeProofs.Rust.SourceLoanSafeCalls
public import SubtreeProofs.Rust.SourceCallRootPreservation

/-! Preserve original loan families through actual calls with closed outputs.
Argument moves may clear family members; unchanged members retain their exact
local resources through the existing suspended-context preservation contract. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem OriginalLoanMachine.advance_call {before world final : World} {active after : Activation}
    {callers : List Activation} {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active)
    {callee : Derived.Callees} {call : Calls}
    (respects : Derived.CallsRespect callee call Derived.TypedReady) (owns : Derived.CallsOwn callee)
    (function : Function) (args : List Operand) {destination : Nat} {binding : Binding} {cost : Cost}
    (root : active.roots destination = some binding) (outside : destination ∉ exceptions)
    (ready : ∀ current suspended packets masks, active.scan world = some current → scanCallers world callers = some suspended →
      Addressed.operands world active.roots (current.loans ++ suspended.reads) active.state args = some (packets, masks) →
      Derived.TypedReady world function packets)
    {values : List Value} {masks : State} (source : SourceEval.operands active.state args = some (values, masks))
    (safe : LoanSafeState masks) (closedMiddle : ClosedOutside exceptions masks)
    (family : ∀ index ∈ exceptions, masks index = active.state index ∨ masks index = .empty)
    (bounded : ∀ index ∈ exceptions, index < active.count)
    {value : Value} {ty : Ty} (typed : SnapshotTyped value ty) (closed : Borrow.Closed ty)
    (state : after.state = masks.set destination (Slot.ofValue value))
    (run : Derived.call callee world active callers function args destination = some (final, after, cost)) :
    OriginalLoanMachine before callers previous external exceptions final after := by
  have checked := Derived.call_spec respects h.native.valid h.native.callersValid h.native.wellFormed function args destination ready run
  have safeAfter : LoanSafeState after.state := by rw [state]; exact safe.set destination (LoanSafe.of_closed (ofValue_typed typed) closed)
  have native := h.native.advance_call respects owns function args root ready run safeAfter
  refine ⟨native, ?_, ?_, ?_⟩
  · rw [state]; exact closedMiddle.set destination (ofValue_typed typed) closed
  · intro index member
    have different : index ≠ destination := by intro same; subst index; exact outside member
    rw [state]
    simp only [Partial.Locals.set, different, ite_false]
    rcases family index member with same | empty
    · rw [same]; exact h.zero index member
    · rw [empty]; simp only [Slot.dropWork]
  · intro index member
    have different : index ≠ destination := by intro same; subst index; exact outside member
    by_cases empty : masks index = .empty
    · exact LoanOrigin.of_closed native.valid before.memory.length index
        (by rw [state]; simpa only [Partial.Locals.set, different, ite_false, empty] using SlotTyped.empty .u32) .u32
    · have same : masks index = active.state index := by rcases family index member with same | missing; exact same; exact False.elim (empty missing)
      obtain ⟨r, represented, bound⟩ := h.origins index member
      have kept := Derived.call_preserves_other_local respects h.native.valid h.native.callersValid h.native.wellFormed
        function args destination ready source same different (bounded index member) represented run
      refine ⟨r, ?_, bound⟩
      rw [checked.2.1]
      exact (represented.transport kept).congr_at (congrFun checked.2.2.2.1 index)
        (by rw [state]; simpa only [Partial.Locals.set, different, ite_false] using same)

end SubtreeProofs.Rust.SourceEval.Addressed
