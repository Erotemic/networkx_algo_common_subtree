module

public import SubtreeProofs.Rust.SourceExpressionOwnerProvenance
public import SubtreeProofs.Rust.SourceEvalAddressedReturn

/-! Evaluator return tuples mix a copied optional witness with a transferred
old memo table. Bound only the witness field's owners; do not require the table
or the complete tuple to have newly allocated descendants. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem CellOwnersAbove.transport {bound : Nat} {before after : Memory} {cell : Cell} {value : Value} {reads : List Nat}
    (above : CellOwnersAbove bound before cell) (graph : Graph before cell value reads)
    (kept : Retains before after reads) : CellOwnersAbove bound after cell := by
  obtain ⟨resources, _, _, represented⟩ := graph.partial.resources
  have oldFoot := (represented.owned.materialize (Slot.materialize_ofValue value)).2
  have next := graph.partial.owner_transport represented.owned kept
  exact CellOwnersAbove.of_footprint (next.materialize (Slot.materialize_ofValue value)).2
    (above resources.owners oldFoot)

def ResultOwnersAbove (bound : Nat) (memory : Memory) (cell : Cell) : Prop :=
  ∃ resultCell tableCell, cell = .node .tuple 0 [resultCell, tableCell] ∧ CellOwnersAbove bound memory resultCell

def LocalResultOwnersAbove (bound : Nat) (world : World) (active : Activation) (slot : Nat) : Prop :=
  ∃ cell, rawAt world active.roots slot = some cell ∧ ResultOwnersAbove bound world.memory cell

theorem ResultOwnersAbove.transport {bound : Nat} {before after : Memory} {cell : Cell} {value : Value} {reads : List Nat}
    (above : ResultOwnersAbove bound before cell) (graph : Graph before cell value reads)
    (kept : Retains before after reads) : ResultOwnersAbove bound after cell := by
  obtain ⟨resultCell, tableCell, rfl, resultFresh⟩ := above
  cases graph with
  | node fields => cases fields with
    | cons resultGraph rest => cases rest with
      | cons tableGraph tail =>
        cases tail
        exact ⟨resultCell, tableCell, rfl, resultFresh.transport resultGraph
          (kept.weaken (fun _ member => List.mem_append_left _ member))⟩

theorem ResultOwnersAbove.of_zero {bound : Nat} {memory : Memory} {cell : Cell} {resultValue tableValue : Value} {reads : List Nat}
    (graph : Graph memory cell (.node .tuple 0 [resultValue, tableValue]) reads)
    (zero : (Slot.ofValue resultValue).dropWork.boxes = 0) : ResultOwnersAbove bound memory cell := by
  cases graph with
  | node fields => cases fields with
    | cons first rest => cases rest with
      | cons second tail =>
        cases tail
        refine ⟨_, _, rfl, ?_⟩
        intro owners footprint address member
        have empty : owners = [] := List.length_eq_zero_iff.mp ((Rep.of_full first.represents footprint).boxes.trans zero)
        rw [empty] at member
        cases member

theorem operand_result_field_owner_provenance {bound : Nat} {world : World} {active : Activation}
    {source : Nat} {guarded : List Nat} {packet : ValueCell} {masks : State}
    (above : LocalResultOwnersAbove bound world active source)
    (run : operand world active.roots guarded active.state (.move (.field (.local source) none 0)) = some (packet, masks)) :
    CellOwnersAbove bound world.memory packet.1 := by
  obtain ⟨rawCell, raw, resultCell, tableCell, rfl, resultFresh⟩ := above
  obtain ⟨pointer, _, located, _⟩ := operand_move_iff.mp run
  cases root : active.roots source with
  | none => simp [rawAt, root] at raw
  | some binding =>
    have read : world.memory[binding.address]? = some (.node .tuple 0 [resultCell, tableCell]) := by
      simpa [rawAt, root] using raw
    have known : Storage.locate world active.roots (.field (.local source) none 0) = some (resultCell, ⟨binding.address, [0]⟩) := by
      simp [Storage.locate, splitPlace, root, read, locatePath, Pointer.field]
    have same := (Prod.mk.inj (Option.some.inj (known.symm.trans located))).1
    exact same ▸ resultFresh

namespace Derived

theorem store_packet_kept {world final : World} {roots : Roots} {frame slot : Nat} {retained : List Nat}
    {masks after : State} {packet : ValueCell} {reads : List Nat}
    (graph : Graph world.memory packet.1 packet.2 reads)
    (run : store world roots frame slot retained masks packet = some (final, after)) :
    rawAt final roots slot = some packet.1 ∧ Retains world.memory final.memory reads := by
  rcases packet with ⟨cell, value⟩
  unfold store at run
  by_cases empty : emptySlot (masks slot) = true
  · cases root : roots slot with
    | none => simp [empty, root] at run
    | some binding =>
      cases written : world.writeStack frame slot binding (retained ++ reads) cell with
      | none => simp [empty, root, graph.trace, written] at run
      | some next =>
        simp only [empty, root, graph.trace, written, bind, Option.bind, ite_true, Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        obtain ⟨_, _, bounded, separated, rfl⟩ := World.writeStack_iff.mp written
        exact ⟨by simp only [rawAt, root, (world.write_spec bounded cell).1, bind, Option.bind],
          (world.write_preserves separated cell).reads.weaken (fun _ member => List.mem_append_right _ member)⟩
  · simp [empty] at run

theorem assign_result_owner_provenance {bound : Nat} {world final : World} {active after : Activation}
    {callers : List Activation} {slot : Nat} {first second : Operand}
    (ha : active.Valid world) (selected : OperandSourcesAbove bound world active [first])
    (run : assign world active callers slot (.aggregate .tuple 0 [first, second]) = some (final, after)) :
    LocalResultOwnersAbove bound final after slot := by
  simp only [assign, bind, Option.bind_eq_some_iff] at run
  obtain ⟨current, currentScan, suspended, callerScan, ⟨packet, masks⟩, expressionRun,
    remainder, remainderScan, ⟨next, state⟩, stored, last⟩ := run
  cases last
  have frame := (Activation.scan_spec ha currentScan).frame
  have packetRead := (expression_readable frame expressionRun).2.1
  simp only [expression, operands, bind, Option.bind_eq_some_iff] at expressionRun
  obtain ⟨⟨packets, masks⟩, arguments, expressionRun⟩ := expressionRun
  obtain ⟨⟨firstPacket, middle⟩, firstRun, ⟨rest, ending⟩, restRun, arguments⟩ := arguments
  obtain ⟨⟨secondPacket, lastMasks⟩, _, ⟨tail, finalMasks⟩, nilRun, restRun⟩ := restRun
  cases nilRun
  cases restRun
  cases arguments
  cases expressionRun
  have firstAbove := (operand_owner_provenance ha firstRun).2 (fun place same => selected first (by simp) place same)
  obtain ⟨reads, graph, _⟩ := packetRead
  obtain ⟨raw, kept⟩ := store_packet_kept graph stored
  refine ⟨_, raw, ?_⟩
  exact (ResultOwnersAbove.transport ⟨firstPacket.1, secondPacket.1, rfl, firstAbove⟩ graph kept)

theorem assign_result_field_owner_provenance {bound : Nat} {world final : World} {active after : Activation}
    {callers : List Activation} {source destination : Nat}
    (ha : active.Valid world) (above : LocalResultOwnersAbove bound world active source)
    (run : assign world active callers destination (.use (.move (.field (.local source) none 0))) = some (final, after)) :
    LocalOwnersAbove bound final after destination := by
  simp only [assign, bind, Option.bind_eq_some_iff] at run
  obtain ⟨current, currentScan, suspended, callerScan, ⟨packet, masks⟩, expressionRun,
    remainder, remainderScan, ⟨next, state⟩, stored, last⟩ := run
  cases last
  have frame := (Activation.scan_spec ha currentScan).frame
  have fresh := operand_result_field_owner_provenance above expressionRun
  obtain ⟨owners, footprint, _⟩ := expression_owners ha expressionRun
  have packetRead := (expression_readable frame expressionRun).2.1
  have exactOwners := store_local_owners packetRead footprint stored
  intro resources represented address member
  rw [exactOwners resources represented] at member
  exact fresh owners footprint address member

theorem return_result_owner_provenance {bound : Nat} {world final : World} {active after : Activation}
    {callers : List Activation} {packet : ValueCell} {cost : Cost}
    (above : LocalResultOwnersAbove bound world active 0)
    (run : returnValue callers world active = some (.returned final after packet, cost)) :
    ResultOwnersAbove bound final.memory packet.1 := by
  simp only [returnValue, bind, Option.bind_eq_some_iff] at run
  obtain ⟨current, _, suspended, _, ⟨actualPacket, masks⟩, moved, last⟩ := run
  cases last
  obtain ⟨cell, raw, fresh⟩ := above
  obtain ⟨pointer, _, located, _⟩ := operand_move_iff.mp moved
  cases root : active.roots 0 with
  | none => simp [rawAt, root] at raw
  | some binding =>
    have read : world.memory[binding.address]? = some cell := by simpa [rawAt, root] using raw
    have known : Storage.locate world active.roots (.local 0) = some (cell, ⟨binding.address, []⟩) := by
      simp [Storage.locate, splitPlace, root, read, locatePath]
    have same := (Prod.mk.inj (Option.some.inj (known.symm.trans located))).1
    exact same ▸ fresh

theorem close_result_owner_provenance {bound : Nat} {world final : World} {active : Activation}
    {callers : List Activation} {guards : List Nat} {packet : ValueCell}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (readable : Readable world.memory world.live packet.1 packet.2)
    (above : ResultOwnersAbove bound world.memory packet.1)
    (run : close world active callers guards packet = some final) : ResultOwnersAbove bound final.memory packet.1 := by
  rw [(close_spec ha hc hw readable run).2.1]
  exact above

end Derived
end SubtreeProofs.Rust.SourceEval.Addressed
