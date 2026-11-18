module

public import SubtreeProofs.Rust.SourceAnchoredLoanMachine
public import SubtreeProofs.Rust.SourceOriginalLoanCalls

/-! Actual calls preserve both original bounded loans and fresh word-supported
loans. The unchanged owning word's complete read footprint is retained by the
callee's suspended-context contract, including its owned Box descendants. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage verified_ordered_core

theorem AnchoredLoanMachine.advance_call {before world final : World} {active after : Activation}
    {callers : List Activation} {previous : Resources} {external original fresh : List Nat}
    {anchorSlot : Nat} {word : BalancedWord} {anchor : Resources}
    (h : AnchoredLoanMachine before callers previous external original fresh anchorSlot word anchor world active)
    {callee : Derived.Callees} {call : Calls}
    (respects : Derived.CallsRespect callee call Derived.TypedReady) (owns : Derived.CallsOwn callee)
    (function : Function) (args : List Operand) {destination : Nat} {binding : Binding} {cost : Cost}
    (root : active.roots destination = some binding) (outside : destination ∉ fresh ++ original)
    (different : anchorSlot ≠ destination)
    (ready : ∀ current suspended packets masks, active.scan world = some current → scanCallers world callers = some suspended →
      Addressed.operands world active.roots (current.loans ++ suspended.reads) active.state args = some (packets, masks) →
      Derived.TypedReady world function packets)
    {values : List Value} {masks : State} (source : SourceEval.operands active.state args = some (values, masks))
    (safe : LoanSafeState masks) (closedMiddle : ClosedOutside (fresh ++ original) masks)
    (family : ∀ index ∈ fresh ++ original, masks index = active.state index ∨ masks index = .empty)
    (bounded : ∀ index ∈ fresh ++ original, index < active.count)
    (anchorSame : masks anchorSlot = active.state anchorSlot)
    {value : Value} {ty : Ty} (typed : SnapshotTyped value ty) (closed : Borrow.Closed ty)
    (state : after.state = masks.set destination (Slot.ofValue value))
    (run : Derived.call callee world active callers function args destination = some (final, after, cost)) :
    AnchoredLoanMachine before callers previous external original fresh anchorSlot word anchor final after := by
  have checked := Derived.call_spec respects h.native.valid h.native.callersValid h.native.wellFormed function args destination ready run
  have safeAfter : LoanSafeState after.state := by rw [state]; exact safe.set destination (LoanSafe.of_closed (ofValue_typed typed) closed)
  have native := h.native.advance_call respects owns function args root ready run safeAfter
  have unchanged : ∀ index, index ≠ destination → masks index = active.state index →
      ∀ resources, LocalResources world active.frame active.roots active.state index resources →
      index < active.count → LocalResources final after.frame after.roots after.state index resources := by
    intro index other same resources represented bound
    have kept := Derived.call_preserves_other_local respects h.native.valid h.native.callersValid h.native.wellFormed
      function args destination ready source same other bound represented run
    rw [checked.2.1]
    exact (represented.transport kept).congr_at (congrFun checked.2.2.2.1 index)
      (by rw [state]; simpa only [Partial.Locals.set, other, ite_false] using same)
  refine ⟨native, ?_, ?_, ?_, ?_, unchanged anchorSlot different anchorSame anchor h.owning h.sourceBound, ?_, ?_⟩
  · rw [state]; exact closedMiddle.set destination (ofValue_typed typed) closed
  · intro index member
    have other : index ≠ destination := by intro same; subst index; exact outside member
    rw [state]
    simp only [Partial.Locals.set, other, ite_false]
    rcases family index member with same | empty
    · rw [same]; exact h.zero index member
    · rw [empty]; simp only [Slot.dropWork]
  · intro index member
    have combined : index ∈ fresh ++ original := List.mem_append_right fresh member
    have other : index ≠ destination := by intro same; subst index; exact outside combined
    by_cases empty : masks index = .empty
    · exact LoanOrigin.of_closed native.valid before.memory.length index
        (by rw [state]; simpa only [Partial.Locals.set, other, ite_false, empty] using SlotTyped.empty .u32) .u32
    · have same : masks index = active.state index := by rcases family index combined with same | missing; exact same; exact False.elim (empty missing)
      obtain ⟨resources, represented, bound⟩ := h.origins index member
      exact ⟨resources, unchanged index other same resources represented (bounded index combined), bound⟩
  · intro index member
    have combined : index ∈ fresh ++ original := List.mem_append_left original member
    have other : index ≠ destination := by intro same; subst index; exact outside combined
    by_cases empty : masks index = .empty
    · exact LoanSupport.of_closed native.valid (· ∈ anchor.reads) index
        (by rw [state]; simpa only [Partial.Locals.set, other, ite_false, empty] using SlotTyped.empty .u32) .u32
    · have same : masks index = active.state index := by rcases family index combined with same | missing; exact same; exact False.elim (empty missing)
      obtain ⟨resources, represented, support⟩ := h.supportedLoans index member
      exact ⟨resources, unchanged index other same resources represented (bounded index combined), support⟩
  · rw [state]
    simpa only [Partial.Locals.set, different, ite_false, anchorSame] using h.value
  · rw [checked.2.2.1]; exact h.sourceBound

end SubtreeProofs.Rust.SourceEval.Addressed
