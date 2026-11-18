module

public import SubtreeProofs.Rust.SourceAnchoredStorage

/-! Closed value assignments and original-data reborrows coexist with fresh
word-supported references. Their selected destination writes retain the exact
owning anchor and both independent reference provenance families. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage verified_ordered_core

theorem AnchoredLoanMachine.assign_empty {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external original fresh : List Nat} {anchorSlot : Nat} {word : BalancedWord} {anchor : Resources}
    (h : AnchoredLoanMachine before callers previous external original fresh anchorSlot word anchor world active)
    {slot : Nat} {binding : Binding} (root : active.roots slot = some binding) (outside : slot ∉ fresh ++ original)
    (different : anchorSlot ≠ slot) (raw : world.memory[binding.address]? = some (.node .tuple 0 []))
    {rhs : Expr} {value : Value} {middle : State}
    (source : SourceEval.expression active.state rhs = some (value, middle)) (empty : middle slot = .empty)
    (closedMiddle : ClosedOutside (fresh ++ original) middle)
    (family : ∀ index ∈ fresh ++ original, middle index = active.state index)
    (anchorSame : middle anchorSlot = active.state anchorSlot)
    (safeMiddle : LoanSafeState middle)
    (moves : ∀ current suspended, Scanned world active current → Callers world callers suspended →
      AllowedExpr world active.roots (current.loans ++ suspended.reads) rhs)
    {ty : Ty} (typed : SnapshotTyped value ty) (closed : Borrow.Closed ty) :
    ∃ cell, Derived.assign world active callers slot rhs = some (world.write binding.address cell,
        {active with state := middle.set slot (Slot.ofValue value)}) ∧
      AnchoredLoanMachine before callers previous external original fresh anchorSlot word anchor
        (world.write binding.address cell) {active with state := middle.set slot (Slot.ofValue value)} := by
  obtain ⟨cell, run, native⟩ := h.native.assign_empty root raw source empty safeMiddle
    (LoanSafe.of_closed (ofValue_typed typed) closed) moves
  let after : Activation := {active with state := middle.set slot (Slot.ofValue value)}
  have masks : ∀ index ∈ fresh ++ original, after.state index = active.state index := by
    intro index member
    have other : index ≠ slot := by intro same; subst index; exact outside member
    simpa only [after, Partial.Locals.set, other, ite_false] using family index member
  have same : after.state anchorSlot = active.state anchorSlot := by
    simpa only [after, Partial.Locals.set, different, ite_false] using anchorSame
  have excluded := h.anchor_avoids_root root different
  refine ⟨cell, run, ⟨native, closedMiddle.set slot (ofValue_typed typed) closed, ?_, ?_, ?_, ?_, same.trans h.value, h.sourceBound⟩⟩
  · intro index member
    change (after.state index).dropWork.boxes = 0
    rw [masks index member]; exact h.zero index member
  · intro index member
    have combined := List.mem_append_right fresh member
    have other : index ≠ slot := by intro same; subst index; exact outside combined
    exact ((h.origins index member).write_other h.native.valid root other (h.zero index combined)
      (h.native.fresh slot binding root) cell).congr (after := after) rfl rfl (masks index combined)
  · intro index member
    have combined := List.mem_append_left original member
    have other : index ≠ slot := by intro same; subst index; exact outside combined
    exact ((h.supportedLoans index member).write_other h.native.valid root other (h.zero index combined) excluded cell).congr
      (after := after) rfl rfl (masks index combined)
  · exact (h.owning.transport (world.write_preserves excluded cell)).congr_at rfl same

theorem AnchoredLoanMachine.assign_original_view {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external original fresh : List Nat} {anchorSlot : Nat} {word : BalancedWord} {anchor : Resources}
    (h : AnchoredLoanMachine before callers previous external original fresh anchorSlot word anchor world active)
    {slot destination : Nat} (member : slot ∈ original) (outside : destination ∉ fresh ++ original) (different : anchorSlot ≠ destination)
    {path : List Projection} {place : Place} (split : splitPlace place = (slot, path))
    (route : SharedRoute (active.state slot) path) {value : Value} (source : active.state.read place = some value)
    (data : NativeData value) {binding : Binding} (root : active.roots destination = some binding)
    (raw : world.memory[binding.address]? = some (.node .tuple 0 [])) (empty : active.state destination = .empty) :
    ∃ pointer, Derived.assign world active callers destination (.address place) =
        some (world.write binding.address (.shared pointer), {active with state := active.state.set destination (.shared value)}) ∧
      AnchoredLoanMachine before callers previous external (destination :: original) fresh anchorSlot word anchor
        (world.write binding.address (.shared pointer)) {active with state := active.state.set destination (.shared value)} ∧
      (world.write binding.address (.shared pointer)).memory[binding.address]? = some (.shared pointer) := by
  obtain ⟨pointer, loans, borrow, graph, bound⟩ := (h.origins slot member).borrow_shared route split source h.native.valid
  obtain ⟨run, native⟩ := h.native.assign_packet_empty (rhs := .address place) (packet := (.shared pointer, .reference value)) root raw
    (fun _ _ _ _ => by simp only [Addressed.expression, source, borrow, bind, Option.bind]) empty h.native.safe
    (by simpa only [Slot.ofValue] using LoanSafe.shared data)
  simp only [Slot.ofValue] at run native
  let final := world.write binding.address (.shared pointer)
  let after : Activation := {active with state := active.state.set destination (.shared value)}
  have memory : final.memory[binding.address]? = some (.shared pointer) :=
    (world.write_spec (List.getElem?_eq_some_iff.mp raw).choose _).1
  have clear : binding.address ∉ loans := by
    intro forbidden
    have old := bound _ forbidden
    have freshRoot := h.native.fresh destination binding root
    omega
  have origin : LoanOrigin final after before.memory.length destination :=
    LoanOrigin.of_shared_graph native.valid root memory (by simp only [after, Partial.Locals.set, ite_true])
      (graph.transport (world.write_preserves clear (.shared pointer)).reads) bound
  have excluded := h.anchor_avoids_root root different
  refine ⟨pointer, run, ⟨native, ?_, ?_, ?_, ?_, ?_, ?_, h.sourceBound⟩, memory⟩
  · exact (h.closed.enlarge (by
      intro index entry
      simp only [List.mem_append, List.mem_cons] at entry ⊢
      tauto)).set_exception (by simp) _
  · intro index entry
    by_cases same : index = destination
    · subst index; simp only [Partial.Locals.set, ite_true, Slot.dropWork]
    · have oldMember : index ∈ fresh ++ original := by
        simpa only [List.mem_append, List.mem_cons, same, false_or] using entry
      simpa only [Partial.Locals.set, same, ite_false] using h.zero index oldMember
  · intro index entry
    rcases List.mem_cons.mp entry with same | oldMember
    · subst index; exact origin
    · have combined := List.mem_append_right fresh oldMember
      have other : index ≠ destination := by intro same; subst index; exact outside combined
      exact ((h.origins index oldMember).write_other h.native.valid root other (h.zero index combined)
        (h.native.fresh destination binding root) (.shared pointer)).congr (after := after) rfl rfl
        (by simp only [after, Partial.Locals.set, other, ite_false])
  · intro index entry
    have combined := List.mem_append_left original entry
    have other : index ≠ destination := by intro same; subst index; exact outside combined
    exact ((h.supportedLoans index entry).write_other h.native.valid root other (h.zero index combined) excluded (.shared pointer)).congr
      (after := after) rfl rfl (by simp only [after, Partial.Locals.set, other, ite_false])
  · exact (h.owning.transport (world.write_preserves excluded (.shared pointer))).congr_at rfl
      (by simp only [Partial.Locals.set, different, ite_false])
  · simpa only [after, Partial.Locals.set, different, ite_false] using h.value

end SubtreeProofs.Rust.SourceEval.Addressed
