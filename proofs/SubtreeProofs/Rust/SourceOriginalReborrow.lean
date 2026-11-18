module

public import SubtreeProofs.Rust.SourceOriginalLoanMachine
public import SubtreeProofs.Rust.SourceSharedRoute
public import SubtreeProofs.Rust.SourceReferenceCopy

/-! Construct shared reborrow assignments while extending an original-loan
family. The selected route crosses an existing shared reference, so the new
view borrows only pre-entry data, even when it refers to an owned Box field. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem OriginalLoanMachine.assign_borrow {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active)
    {slot destination : Nat} (member : slot ∈ exceptions) (outside : destination ∉ exceptions)
    {path : List Projection} {place : Place} (split : splitPlace place = (slot, path))
    (route : SharedRoute (active.state slot) path) {value : Value} (source : active.state.read place = some value)
    (data : NativeData value) {binding : Binding} (bound : active.roots destination = some binding)
    (raw : world.memory[binding.address]? = some (.node .tuple 0 [])) (empty : active.state destination = .empty) :
    ∃ pointer,
      Derived.assign world active callers destination (.address place) =
        some (world.write binding.address (.shared pointer), {active with state := active.state.set destination (.shared value)}) ∧
      OriginalLoanMachine before callers previous external (destination :: exceptions)
        (world.write binding.address (.shared pointer)) {active with state := active.state.set destination (.shared value)} ∧
      (world.write binding.address (.shared pointer)).memory[binding.address]? = some (.shared pointer) := by
  obtain ⟨pointer, loans, borrow, graph, old⟩ := (h.origins slot member).borrow_shared route split source h.native.valid
  obtain ⟨run, native⟩ := h.native.assign_packet_empty (rhs := .address place) (packet := (.shared pointer, .reference value)) bound raw
    (fun _ _ _ _ => by simp only [Addressed.expression, source, borrow, bind, Option.bind]) empty h.native.safe
    (by simpa only [Slot.ofValue] using LoanSafe.shared data)
  simp only [Slot.ofValue] at run native
  let final := world.write binding.address (.shared pointer)
  let after : Activation := {active with state := active.state.set destination (.shared value)}
  change LoanSafeMachine before callers previous external final after at native
  have memory : final.memory[binding.address]? = some (.shared pointer) :=
    (world.write_spec (List.getElem?_eq_some_iff.mp raw).choose _).1
  have clear : binding.address ∉ loans := by intro forbidden; have small := old _ forbidden; have fresh := h.native.fresh destination binding bound; omega
  have origin : LoanOrigin final after before.memory.length destination :=
    LoanOrigin.of_shared_graph native.valid bound memory (by simp only [after, Partial.Locals.set, ite_true])
      (graph.transport (world.write_preserves clear (.shared pointer)).reads) old
  refine ⟨pointer, run, ⟨native, ?_, ?_, ?_⟩, memory⟩
  · exact (h.closed.enlarge (fun _ entry => List.mem_cons_of_mem _ entry)).set_exception (by simp) _
  · intro index entry
    rcases List.mem_cons.mp entry with same | oldMember
    · subst index; simp only [Partial.Locals.set, ite_true, Slot.dropWork]
    · have different : index ≠ destination := by intro same; subst index; exact outside oldMember
      simpa only [after, Partial.Locals.set, different, ite_false] using h.zero index oldMember
  · intro index entry
    rcases List.mem_cons.mp entry with same | oldMember
    · subst index; exact origin
    · have different : index ≠ destination := by intro same; subst index; exact outside oldMember
      exact ((h.origins index oldMember).write_other h.native.valid bound different (h.zero index oldMember)
        (h.native.fresh destination binding bound) (.shared pointer)).congr
        (after := after) rfl rfl (by simp only [after, Partial.Locals.set, different, ite_false])

end SubtreeProofs.Rust.SourceEval.Addressed
