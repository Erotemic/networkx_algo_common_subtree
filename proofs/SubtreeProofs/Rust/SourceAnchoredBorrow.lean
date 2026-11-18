module

public import SubtreeProofs.Rust.SourceAnchoredLoanMachine

/-! Construct actual fresh native references into a closed owning word. The
new reference is supported by the word's precise resource reads; original
query origins and all previously scoped references retain their provenance. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage verified_ordered_core

theorem AnchoredLoanMachine.assign_scoped_borrow {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external original fresh : List Nat} {source : Nat} {word : BalancedWord} {anchor : Resources}
    (h : AnchoredLoanMachine before callers previous external original fresh source word anchor world active)
    {destination : Nat} (outside : destination ∉ fresh ++ original) (different : source ≠ destination)
    {place : Place} {value : Value} (sourceValue : active.state.read place = some value) (data : NativeData value)
    {pointer : Pointer} {reads : List Nat} (borrow : Storage.borrow world active.roots place = some (.shared pointer))
    (graph : Graph world.memory (.shared pointer) (.reference value) reads) (supported : reads ⊆ anchor.reads)
    {binding : Binding} (root : active.roots destination = some binding)
    (raw : world.memory[binding.address]? = some (.node .tuple 0 [])) (empty : active.state destination = .empty) :
    Derived.assign world active callers destination (.address place) =
        some (world.write binding.address (.shared pointer), {active with state := active.state.set destination (.shared value)}) ∧
      AnchoredLoanMachine before callers previous external original (destination :: fresh) source word anchor
        (world.write binding.address (.shared pointer)) {active with state := active.state.set destination (.shared value)} ∧
      (world.write binding.address (.shared pointer)).memory[binding.address]? = some (.shared pointer) := by
  obtain ⟨run, native⟩ := h.native.assign_packet_empty (rhs := .address place) (packet := (.shared pointer, .reference value)) root raw
    (fun _ _ _ _ => by simp only [Addressed.expression, sourceValue, borrow, bind, Option.bind]) empty h.native.safe
    (by simpa only [Slot.ofValue] using LoanSafe.shared data)
  simp only [Slot.ofValue] at run native
  let final := world.write binding.address (.shared pointer)
  let after : Activation := {active with state := active.state.set destination (.shared value)}
  have memory : final.memory[binding.address]? = some (.shared pointer) :=
    (world.write_spec (List.getElem?_eq_some_iff.mp raw).choose _).1
  have excluded := h.anchor_avoids_root root different
  have kept : Preserves world final anchor.reads := world.write_preserves excluded (.shared pointer)
  have clear : binding.address ∉ reads := fun member => excluded (supported member)
  have origin : LoanSupport final after (· ∈ anchor.reads) destination :=
    LoanSupport.of_shared_graph native.valid root memory (by simp only [after, Partial.Locals.set, ite_true])
      (graph.transport (world.write_preserves clear (.shared pointer)).reads) (fun _ member => supported member)
  refine ⟨run, ⟨native, ?_, ?_, ?_, ?_, ?_, ?_, h.sourceBound⟩, memory⟩
  · exact (h.closed.enlarge (fun _ member => by simpa only [List.cons_append, List.mem_cons] using Or.inr member)).set_exception (by simp) _
  · intro slot member
    by_cases same : slot = destination
    · subst slot; simp only [Partial.Locals.set, ite_true, Slot.dropWork]
    · have oldMember : slot ∈ fresh ++ original := by simpa only [List.cons_append, List.mem_cons, same, false_or] using member
      simpa only [Partial.Locals.set, same, ite_false] using h.zero slot oldMember
  · intro slot member
    have other : slot ≠ destination := by intro same; subst slot; exact outside (List.mem_append_right fresh member)
    exact ((h.origins slot member).write_other h.native.valid root other (h.zero slot (List.mem_append_right fresh member))
      (h.native.fresh destination binding root) (.shared pointer)).congr (after := after) rfl rfl
      (by simp only [after, Partial.Locals.set, other, ite_false])
  · intro slot member
    rcases List.mem_cons.mp member with same | oldMember
    · subst slot; exact origin
    · have other : slot ≠ destination := by intro same; subst slot; exact outside (List.mem_append_left original oldMember)
      exact ((h.supportedLoans slot oldMember).write_other h.native.valid root other (h.zero slot (List.mem_append_left original oldMember)) excluded
        (.shared pointer)).congr (after := after) rfl rfl (by simp only [after, Partial.Locals.set, other, ite_false])
  · exact (h.owning.transport kept).congr_at rfl (by simp only [Partial.Locals.set, different, ite_false])
  · simpa only [after, Partial.Locals.set, different, ite_false] using h.value

theorem AnchoredLoanMachine.assign_owned_view {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external original fresh : List Nat} {source : Nat} {word : BalancedWord} {anchor : Resources}
    (h : AnchoredLoanMachine before callers previous external original fresh source word anchor world active)
    {destination : Nat} (outside : destination ∉ fresh ++ original) (different : source ≠ destination)
    {place : Place} {path : List Projection} (split : splitPlace place = (source, path))
    {value : Value} (sourceValue : active.state.read place = some value) (data : NativeData value)
    {binding : Binding} (root : active.roots destination = some binding)
    (raw : world.memory[binding.address]? = some (.node .tuple 0 [])) (empty : active.state destination = .empty) :
    ∃ pointer, Derived.assign world active callers destination (.address place) =
        some (world.write binding.address (.shared pointer), {active with state := active.state.set destination (.shared value)}) ∧
      AnchoredLoanMachine before callers previous external original (destination :: fresh) source word anchor
        (world.write binding.address (.shared pointer)) {active with state := active.state.set destination (.shared value)} ∧
      (world.write binding.address (.shared pointer)).memory[binding.address]? = some (.shared pointer) := by
  obtain ⟨pointer, reads, borrow, graph, supported⟩ := h.owning.borrow_source split sourceValue
  exact ⟨pointer, h.assign_scoped_borrow outside different sourceValue data borrow graph supported root raw empty⟩

end SubtreeProofs.Rust.SourceEval.Addressed
