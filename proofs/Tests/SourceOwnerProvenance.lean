module

import SubtreeProofs.Rust.SourceHelperOwnerProvenance
import all SubtreeProofs.Rust.SourcePartialValue
import all SubtreeProofs.Rust.SourcePartialMoves

@[expose] section

namespace SourceOwnerProvenanceTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage
open SourceEval.Addressed verified_ordered_core

private def witness : CommonEmbedding := ⟨.Pair .Empty .Empty, 7#u32⟩
private def table : MemoTable := .Entry ⟨.Empty, .Empty, witness⟩ .Empty
private def entry : Cell := .node .entry 0 [.node .word 0 [], .node .word 0 [],
  .node .embedding 0 [.node .word 1 [.owned 0, .owned 1], .number 7]]
private def base : World := ⟨[.node .word 0 [], .node .word 0 [], entry, .node .table 0 []],
  fun address => if address < 4 then some .box else none, fun address => decide (address < 4)⟩
private def tableCell : Cell := .node .table 1 [.owned 2, .owned 3]
private def query : Cell := .shared ⟨2, [0]⟩
private def resultView : Cell := .shared ⟨2, [2]⟩
private def packets : List ValueCell := [(tableCell, encodeTable table), (query, .reference (encodeWord .Empty)),
  (resultView, .reference (encodeResult witness))]
private def world := base.stackCells 4 (packets.map Prod.fst)
private def active := initialActivation base 4 5 packets

private theorem base_valid : base.WellFormed := by
  constructor
  · intro address
    by_cases bound : address < 4 <;> simp [base, bound]
  · intro address live
    exact of_decide_eq_true live
private theorem entry_graph : Graph base.memory entry
    (.node .entry 0 [encodeWord .Empty, encodeWord .Empty, encodeResult witness]) [0, 1] :=
  .node (.cons (.node .nil) (.cons (.node .nil) (.cons (.node (.cons
    (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil))) (.cons (.number 7) .nil))) .nil)))
private theorem table_graph : Graph base.memory tableCell (encodeTable table) [0, 1, 2, 3] :=
  .node (.cons (.owned rfl entry_graph) (.cons (.owned rfl (.node .nil)) .nil))
private theorem packets_readable : ∀ packet ∈ packets, Readable base.memory base.live packet.1 packet.2 := by
  intro packet member
  simp only [packets, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨[0, 1, 2, 3], table_graph, by simp [AliveOn, base]⟩
  · exact ⟨[2], .shared rfl (.node .nil), by simp [AliveOn, base]⟩
  · exact ⟨[0, 1, 2], .shared rfl (.node (.cons
      (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil))) (.cons (.number 7) .nil))),
      by simp [AliveOn, base]⟩
private theorem active_valid : active.Valid world := initialActivation_valid base_valid 4 5 packets_readable (by decide +kernel)
private theorem world_valid : world.WellFormed := base_valid.stackCells _ _

private def copyPackets : List ValueCell := [(resultView, .reference (encodeResult witness))]
private theorem copy_readable : ∀ packet ∈ copyPackets, Readable world.memory world.live packet.1 packet.2 := by
  intro packet member
  have same : packet = (resultView, .reference (encodeResult witness)) := by simpa [copyPackets] using member
  subst packet
  obtain ⟨reads, graph, alive⟩ := packets_readable (resultView, .reference (encodeResult witness)) (by simp [packets])
  have kept := base.stackCells_keeps base_valid 4 (packets.map Prod.fst) reads
  exact ⟨reads, graph.mono kept.memory, fun address member => kept.alive address member (alive address member)⟩
private theorem copy_ready : Derived.TypedReady world .copyResult copyPackets :=
  ⟨[.shared (.adt .embedding)], .adt .embedding, .cons (.shared (result_typed witness)) .nil, by with_unfolding_all rfl⟩

-- A nonempty cached witness is read through an alias into the still-owned
-- input table. The actual helper owns two fresh Boxes and preserves old ones.
example : ∃ final packet cost owners,
    Helpers.callee 8 32 world [] [] .copyResult copyPackets = some (final, packet, cost) ∧
    Footprint final.memory packet.1 owners ∧ owners.length = 2 ∧
    (∀ address ∈ owners, world.memory.length ≤ address) ∧ final.live 0 = true ∧ final.live 1 = true := by
  have existsRun : (Helpers.callee 8 32 world [] [] .copyResult copyPackets).isSome = true := by decide +kernel
  obtain ⟨⟨final, packet, cost⟩, run⟩ := Option.isSome_iff_exists.mp existsRun
  obtain ⟨owners, footprint, fresh⟩ := Helpers.callee_fresh_output 8 32 world_valid (by simp [Helpers.FreshOutputHelper]) copy_readable copy_ready run
  have concrete : final.memory.length = 9 ∧ final.live 0 = true ∧ final.live 1 = true ∧
      (traceResources final.memory packet.1 (Slot.ofValue packet.2)).map (fun r => r.owners.length) = some 2 := by
    have eq : (Helpers.callee 8 32 world [] [] .copyResult copyPackets).map (fun (w, p, _) =>
        (w.memory.length, w.live 0, w.live 1, (traceResources w.memory p.1 (Slot.ofValue p.2)).map (fun r => r.owners.length))) =
        some (9, true, true, some 2) := by decide +kernel
    rw [run] at eq
    simpa only [Option.map_some, Option.some.injEq, Prod.mk.injEq] using eq
  have packetRead := (Helpers.callee_typed_respects 8 32 world [] [] .copyResult copyPackets final packet cost
    world_valid copy_readable (by simp) (by simp [AliveOn]) copy_ready run).2.1
  obtain ⟨reads, graph, _⟩ := packetRead
  obtain ⟨r, trace, _, represented⟩ := graph.partial.resources
  have same := Rep.unique represented.owned (Rep.of_full graph.represents footprint)
  have length : owners.length = 2 := by
    rw [trace] at concrete
    simpa only [Option.map_some, Option.some.injEq, same] using concrete.2.2.2
  exact ⟨final, packet, cost, owners, run, footprint, length, fresh, concrete.2.1, concrete.2.2.1⟩

private def preparedWorld := world.allocate (.stack 4 0 world.memory.length) (.node .tuple 0 [])
private def prepared : Activation :=
  {active with roots := active.roots.set 0 (some ⟨world.memory.length, world.memory.length⟩), state := active.state.set 0 .empty}
private theorem opened : Derived.storageLive world active [] 0 = some (preparedWorld, prepared) := by with_unfolding_all rfl
private theorem prepared_valid : prepared.Valid preparedWorld := (Derived.storageLive_spec active_valid (by simp) world_valid opened).valid
private theorem prepared_world_valid : preparedWorld.WellFormed := world_valid.allocate _ _
private def copyArgs : List SourceEval.Operand := [.move (.local 3)]
private theorem copy_arguments : SourceEval.operands prepared.state copyArgs =
    some ([.reference (encodeResult witness)], prepared.state.set 3 .empty) := by with_unfolding_all rfl

-- Full derived-call argument extraction and guarded destination storage keep
-- the clone's owner provenance. The owned table and its original aliases live.
example : ∃ final after cost,
    Derived.call (Recursive.original 32 8) preparedWorld prepared [] .copyResult copyArgs 0 = some (final, after, cost) ∧
    LocalOwnersAbove preparedWorld.memory.length final after 0 ∧ (after.state 0).dropWork.boxes = 2 ∧
    final.live 0 = true ∧ final.live 1 = true := by
  have existsRun : (Derived.call (Recursive.original 32 8) preparedWorld prepared [] .copyResult copyArgs 0).isSome = true := by decide +kernel
  obtain ⟨⟨final, after, cost⟩, run⟩ := Option.isSome_iff_exists.mp existsRun
  have ready := Derived.call_ready_from_values (callers := []) prepared_valid copy_arguments
    (.cons (.shared (result_typed witness)) .nil)
    (show SourceEval.Types.callOutput .copyResult [.shared (.adt .embedding)] = some (.adt .embedding) by with_unfolding_all rfl)
  have fresh := Derived.original_helper_call_fresh_output 8 32 (by decide) prepared_valid (by simp)
    prepared_world_valid (by simp [Helpers.FreshOutputHelper]) ready run
  have concrete : (after.state 0).dropWork.boxes = 2 ∧ final.live 0 = true ∧ final.live 1 = true := by
    have eq : (Derived.call (Recursive.original 32 8) preparedWorld prepared [] .copyResult copyArgs 0).map (fun (w, a, _) =>
        ((a.state 0).dropWork.boxes, w.live 0, w.live 1)) = some (2, true, true) := by decide +kernel
    rw [run] at eq
    simpa only [Option.map_some, Option.some.injEq, Prod.mk.injEq] using eq
  exact ⟨final, after, cost, run, fresh, concrete⟩

example : ¬ Helpers.FreshOutputHelper .insert ∧ ¬ Helpers.FreshOutputHelper .boxNew := by simp [Helpers.FreshOutputHelper]


private def lookupPackets : List ValueCell :=
  [(.shared ⟨4, []⟩, .reference (encodeTable table)), (query, .reference (encodeWord .Empty)), (query, .reference (encodeWord .Empty))]
private theorem lookup_readable : ∀ packet ∈ lookupPackets, Readable world.memory world.live packet.1 packet.2 := by
  intro packet member
  simp only [lookupPackets, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · have graph := table_graph.mono (base.stackCells_keeps base_valid 4 (packets.map Prod.fst) [0, 1, 2, 3]).memory
    exact ⟨[0, 1, 2, 3, 4], .shared rfl graph, by simp [AliveOn, world, World.stackCells, base, packets]⟩
  all_goals
    obtain ⟨reads, graph, alive⟩ := packets_readable (query, .reference (encodeWord .Empty)) (by simp [packets])
    have kept := base.stackCells_keeps base_valid 4 (packets.map Prod.fst) reads
    exact ⟨reads, graph.mono kept.memory, fun address member => kept.alive address member (alive address member)⟩
private theorem lookup_ready : Derived.TypedReady world .lookup lookupPackets :=
  ⟨[.shared (.adt .table), .shared (.adt .word), .shared (.adt .word)], .adt .optional,
    .cons (.shared (table_typed table)) (.cons (.shared (word_typed .Empty)) (.cons (.shared (word_typed .Empty)) .nil)),
    by with_unfolding_all rfl⟩

-- Lookup clones a nonempty cached witness while both query references repeat
-- one table-owned address. Only the cloned option's owners are newly allocated.
set_option maxRecDepth 8192 in
example : ∃ final packet cost owners,
    Helpers.callee 8 32 world [] [] .lookup lookupPackets = some (final, packet, cost) ∧
    packet.2 = encodeOption (some witness) ∧ Footprint final.memory packet.1 owners ∧
    owners.length = 2 ∧ (∀ address ∈ owners, world.memory.length ≤ address) ∧
    final.live 0 = true ∧ final.live 1 = true := by
  have existsRun : (Helpers.callee 8 32 world [] [] .lookup lookupPackets).isSome = true := by decide +kernel
  obtain ⟨⟨final, packet, cost⟩, run⟩ := Option.isSome_iff_exists.mp existsRun
  obtain ⟨owners, footprint, fresh⟩ := Helpers.callee_fresh_output 8 32 world_valid (by simp [Helpers.FreshOutputHelper]) lookup_readable lookup_ready run
  have concrete : packet.2 = encodeOption (some witness) ∧ final.live 0 = true ∧ final.live 1 = true := by
    have eq : (Helpers.callee 8 32 world [] [] .lookup lookupPackets).map (fun (w, p, _) => (p.2, w.live 0, w.live 1)) =
        some (encodeOption (some witness), true, true) := by with_unfolding_all rfl
    rw [run] at eq
    simpa only [Option.map_some, Option.some.injEq, Prod.mk.injEq] using eq
  have packetRead := (Helpers.callee_typed_respects 8 32 world [] [] .lookup lookupPackets final packet cost
    world_valid lookup_readable (by simp) (by simp [AliveOn]) lookup_ready run).2.1
  obtain ⟨reads, graph, _⟩ := packetRead
  have length := (Rep.of_full graph.represents footprint).boxes
  rw [concrete.1] at length
  have boxes : (Slot.ofValue (encodeOption (some witness))).dropWork.boxes = 2 := by with_unfolding_all rfl
  have two : owners.length = 2 := length.trans boxes
  exact ⟨final, packet, cost, owners, run, concrete.1, footprint, two, fresh, concrete.2⟩


private def insertPackets : List ValueCell := [(tableCell, encodeTable table), (query, .reference (encodeWord .Empty)),
  (query, .reference (encodeWord .Empty)), (resultView, .reference (encodeResult witness))]
private theorem insert_readable : ∀ packet ∈ insertPackets, Readable world.memory world.live packet.1 packet.2 := by
  intro packet member
  have inWorld : ∀ packet ∈ packets, Readable world.memory world.live packet.1 packet.2 := by
    intro packet member
    obtain ⟨reads, graph, alive⟩ := packets_readable packet member
    have kept := base.stackCells_keeps base_valid 4 (packets.map Prod.fst) reads
    exact ⟨reads, graph.mono kept.memory, fun address member => kept.alive address member (alive address member)⟩
  simp only [insertPackets, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> exact inWorld _ (by simp [packets])
private theorem insert_ready : Derived.TypedReady world .insert insertPackets :=
  ⟨[.adt .table, .shared (.adt .word), .shared (.adt .word), .shared (.adt .embedding)], .adt .table,
    .cons (table_typed table) (.cons (.shared (word_typed .Empty)) (.cons (.shared (word_typed .Empty))
      (.cons (.shared (result_typed witness)) .nil))), by with_unfolding_all rfl⟩

-- The exclusion of insertion is substantive: its output still owns old input
-- table Boxes while their original query/witness aliases remain live.
example : ∃ final packet cost owners,
    Helpers.callee 8 32 world [] [] .insert insertPackets = some (final, packet, cost) ∧
    Footprint final.memory packet.1 owners ∧ (∃ address ∈ owners, address < world.memory.length) := by
  have existsRun : (Helpers.callee 8 32 world [] [] .insert insertPackets).isSome = true := by decide +kernel
  obtain ⟨⟨final, packet, cost⟩, run⟩ := Option.isSome_iff_exists.mp existsRun
  have tableFoot := table_graph.footprint (Borrow.typed_unborrowed (table_graph.represents.typed (table_typed table)) (.adt .table))
  have input : FieldsFootprint world.memory (insertPackets.map Prod.fst) [0, 1, 2, 3] :=
    .cons (Heap.Spatial.footprint_mono (base.stackCells_keeps base_valid 4 (packets.map Prod.fst) []).memory tableFoot)
      (.cons (.shared _) (.cons (.shared _) (.cons (.shared _) .nil)))
  obtain ⟨owners, footprint, permutation, _, _⟩ := Helpers.callee_owner_ledger 8 32 world_valid .insert insertPackets
    insert_readable insert_ready input run
  refine ⟨final, packet, cost, owners, run, footprint, 0, permutation.symm.subset ?_, by decide +kernel⟩
  exact List.mem_append_left _ (by simp)

end SourceOwnerProvenanceTests
