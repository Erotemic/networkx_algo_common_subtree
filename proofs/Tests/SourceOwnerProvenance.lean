module

import SubtreeProofs.Rust.SourceHelperOwnerProvenance
import SubtreeProofs.Rust.SourceRetainedOwnerProvenance
import SubtreeProofs.Rust.SourceEmptyOwnerProvenance
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

set_option maxRecDepth 8192

private def copiedCell : Cell := .node .embedding 0 [.node .word 1 [.owned 8, .owned 9], .number 7]
private def copiedWorld := (preparedWorld.boxSuffix (preparedWorld.memory ++ [.node .word 0 [], .node .word 0 []])).write 7 copiedCell
private def copied : Activation := {prepared with state := (prepared.state.set 3 .empty).set 0 (Slot.ofValue (encodeResult witness))}
private theorem copied_run : ∃ cost : SourceEval.Cost,
    Derived.call (Recursive.original 32 8) preparedWorld prepared [] .copyResult copyArgs 0 = some (copiedWorld, copied, cost) := by
  refine ⟨?cost, ?run⟩
  case run => with_unfolding_all rfl
private theorem copied_checked : copied.Valid copiedWorld ∧ copiedWorld.WellFormed ∧
    LocalOwnersAbove preparedWorld.memory.length copiedWorld copied 0 := by
  obtain ⟨cost, run⟩ := copied_run
  have ready := Derived.call_ready_from_values (callers := []) prepared_valid copy_arguments
    (.cons (.shared (result_typed witness)) .nil)
    (show SourceEval.Types.callOutput .copyResult [.shared (.adt .embedding)] = some (.adt .embedding) by with_unfolding_all rfl)
  have checked := Derived.call_spec (Recursive.original_typed_respects 32 8) prepared_valid (by simp) prepared_world_valid .copyResult copyArgs 0 ready run
  exact ⟨checked.2.2.2.2.1, checked.2.2.2.2.2.2.1,
    Derived.original_helper_call_fresh_output 8 32 (by decide) prepared_valid (by simp) prepared_world_valid
      (by simp [Helpers.FreshOutputHelper]) ready run⟩

private def wordCell : Cell := .node .word 1 [.owned 8, .owned 9]
private def openedWorld := copiedWorld.allocate (.stack 4 4 10) (.node .tuple 0 [])
private def openedActive : Activation := {copied with roots := copied.roots.set 4 (some ⟨10, 10⟩), state := copied.state.set 4 .empty}
private theorem opened_step : Derived.storageLive copiedWorld copied [] 4 = some (openedWorld, openedActive) := by with_unfolding_all rfl
private def wordWorld := openedWorld.write 10 wordCell
private def wordActive : Activation := {openedActive with state :=
  (openedActive.state.set 0 (.node .embedding 0 [.empty, .number 7])).set 4 (Slot.ofValue (encodeWord (.Pair .Empty .Empty)))}
private def wordExpr : SourceEval.Expr := .use (.move (.field (.local 0) none 0))
private theorem word_step : Derived.assign openedWorld openedActive [] 4 wordExpr = some (wordWorld, wordActive) := by with_unfolding_all rfl
private def droppedWorld := wordWorld.retire []
private def droppedActive : Activation := {wordActive with state := wordActive.state.set 0 .empty}
private theorem dropped_step : Derived.drop wordWorld wordActive [] 0 = some (droppedWorld, droppedActive) := by with_unfolding_all rfl
private def embeddingWorld := droppedWorld.write 6 copiedCell
private def embeddingActive : Activation := {droppedActive with state := (droppedActive.state.set 4 .empty).set 3 (Slot.ofValue (encodeResult witness))}
private def embeddingExpr : SourceEval.Expr := .aggregate .embedding 0 [.move (.local 4), .number 7]
private theorem embedding_step : Derived.assign droppedWorld droppedActive [] 3 embeddingExpr = some (embeddingWorld, embeddingActive) := by with_unfolding_all rfl
private def optionCell : Cell := .node .optional 1 [copiedCell]
private def optionWorld := embeddingWorld.write 10 optionCell
private def optionActive : Activation := {embeddingActive with state := (embeddingActive.state.set 3 .empty).set 4 (Slot.ofValue (encodeOption (some witness)))}
private def optionExpr : SourceEval.Expr := .aggregate .optional 1 [.move (.local 3)]
private theorem option_step : Derived.assign embeddingWorld embeddingActive [] 4 optionExpr = some (optionWorld, optionActive) := by with_unfolding_all rfl
private def outputCell : Cell := .node .tuple 0 [optionCell, tableCell]
private def outputWorld := optionWorld.write 7 outputCell
private def outputActive : Activation :=
  {optionActive with state := ((optionActive.state.set 4 .empty).set 1 .empty).set 0 (Slot.ofValue (SourceEval.Evaluator.encodeOutput (some witness) table))}
private theorem output_step : Derived.assign optionWorld optionActive [] 0 (.aggregate .tuple 0 [.move (.local 4), .move (.local 1)]) =
    some (outputWorld, outputActive) := by with_unfolding_all rfl
private def returned : Activation := {outputActive with state := outputActive.state.set 0 .empty}
private def outputPacket : ValueCell := (outputCell, SourceEval.Evaluator.encodeOutput (some witness) table)
private theorem returned_step : Derived.returnValue [] outputWorld outputActive =
    some (.returned outputWorld returned outputPacket, SourceEval.Cost.local 1) := by with_unfolding_all rfl
private def closedWorld := outputWorld.retire returned.stackAddresses
private theorem closed_step : close outputWorld returned [] [] outputPacket = some closedWorld := by with_unfolding_all rfl

private theorem checked_assignment {w next : World} {a after : Activation} {slot : Nat} {rhs : SourceEval.Expr}
    (ha : a.Valid w) (hw : w.WellFormed) (run : Derived.assign w a [] slot rhs = some (next, after)) :
    after.Valid next ∧ next.WellFormed := by
  have checked := Derived.assign_spec ha (by simp) hw (fun _ _ => none) slot rhs run
  exact ⟨checked.2.2.2.2.1, checked.2.2.2.2.2.2.1⟩

-- A real nonempty cache clone passes through a partial field move, zero-owner
-- shell drop, embedding/option reconstruction, a mixed old-table return tuple,
-- actual return extraction and stack closure. Only its witness field is fresh.
private theorem output_checked : outputActive.Valid outputWorld ∧ outputWorld.WellFormed ∧
    LocalResultOwnersAbove preparedWorld.memory.length outputWorld outputActive 0 := by
  have openedSpec := Derived.storageLive_spec copied_checked.1 (by simp) copied_checked.2.1 opened_step
  have firstFresh := Derived.storageLive_owner_provenance copied_checked.1 copied_checked.2.1 opened_step 0 copied_checked.2.2
  have wordSpec := checked_assignment openedSpec.valid openedSpec.wellFormed word_step
  have wordFresh := Derived.assign_owner_provenance (bound := preparedWorld.memory.length) openedSpec.valid
    (by intro op member place same
        have selected : op = .move (.field (.local 0) none 0) := by simpa [ExpressionSourcesAbove, OperandSourcesAbove, wordExpr] using member
        have pathEq := SourceEval.Operand.move.inj (same.symm.trans selected)
        cases pathEq
        exact firstFresh) word_step
  have dropSpec := Derived.drop_spec wordSpec.1 (by simp) wordSpec.2 dropped_step
  have keptWord := Derived.drop_keeps_owner_provenance wordSpec.1 (by simp) wordSpec.2 (by decide) (by decide) wordFresh dropped_step
  have embeddingSpec := checked_assignment dropSpec.1.valid dropSpec.1.wellFormed embedding_step
  have embeddingFresh := Derived.assign_owner_provenance dropSpec.1.valid
    (by intro op member place same
        have selected : op = .move (.local 4) ∨ op = .number 7 := by simpa [ExpressionSourcesAbove, OperandSourcesAbove, embeddingExpr] using member
        rcases selected with rfl | rfl
        · cases same; exact keptWord
        · cases same) embedding_step
  have optionSpec := checked_assignment embeddingSpec.1 embeddingSpec.2 option_step
  have optionFresh := Derived.assign_owner_provenance embeddingSpec.1
    (by intro op member place same
        have selected : op = .move (.local 3) := by simpa [ExpressionSourcesAbove, OperandSourcesAbove, optionExpr] using member
        have pathEq := SourceEval.Operand.move.inj (same.symm.trans selected)
        cases pathEq
        exact embeddingFresh) option_step
  have outputSpec := checked_assignment optionSpec.1 optionSpec.2 output_step
  have mixed := Derived.assign_result_owner_provenance optionSpec.1
    (by intro op member place same
        have selected : op = .move (.local 4) := by simpa using member
        have pathEq := SourceEval.Operand.move.inj (same.symm.trans selected)
        cases pathEq
        exact optionFresh) output_step
  exact ⟨outputSpec.1, outputSpec.2, mixed⟩

example : ResultOwnersAbove preparedWorld.memory.length closedWorld.memory outputPacket.1 ∧
    outputPacket.2 = SourceEval.Evaluator.encodeOutput (some witness) table ∧
    closedWorld.live 0 = true ∧ closedWorld.live 1 = true ∧ closedWorld.live 8 = true ∧ closedWorld.live 9 = true := by
  have outputSpec := output_checked
  have mixed := outputSpec.2.2
  have packetFresh := Derived.return_result_owner_provenance mixed returned_step
  have returnSpec := Derived.returnValue_spec outputSpec.1 (by simp) outputSpec.2.1 returned_step
  have closedFresh := Derived.close_result_owner_provenance returnSpec.2.2.2.2.1.active (by simp)
    returnSpec.2.2.2.2.1.wellFormed returnSpec.2.2.2.2.1.packet packetFresh closed_step
  exact ⟨closedFresh, rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

private def unpackedWorld := outputWorld.write 6 optionCell
private def unpacked : Activation := {outputActive with state :=
  (outputActive.state.set 0 (.node .tuple 0 [.empty, Slot.ofValue (encodeTable table)])).set 3 (Slot.ofValue (encodeOption (some witness)))}
private theorem unpacked_step : Derived.assign outputWorld outputActive [] 3 (.use (.move (.field (.local 0) none 0))) =
    some (unpackedWorld, unpacked) := by with_unfolding_all rfl

-- Extract only the bounded optional witness from a tuple whose old table
-- owners have no freshness bound. Actual storage yields two bounded owners.
example : LocalOwnersAbove preparedWorld.memory.length unpackedWorld unpacked 3 ∧
    (unpacked.state 3).dropWork.boxes = 2 ∧ (unpacked.state 0).dropWork.boxes = 4 := by
  exact ⟨Derived.assign_result_field_owner_provenance output_checked.1 output_checked.2.2 unpacked_step,
    by with_unfolding_all rfl, by with_unfolding_all rfl⟩

-- Moving the payload through an owned Box keeps that emptied Box shell in
-- the source inventory. Its two remaining owner identities keep their bound.
example : ∃ masks,
    operand wordWorld wordActive.roots [] wordActive.state
      (.move (.deref (.field (.local 4) (some 1) 0))) = some ((.node .word 0 [], encodeWord .Empty), masks) ∧
    LocalOwnersAbove preparedWorld.memory.length wordWorld {wordActive with state := masks} 4 ∧
    (masks 4).dropWork.boxes = 2 := by
  have openedSpec := Derived.storageLive_spec copied_checked.1 (by simp) copied_checked.2.1 opened_step
  have firstFresh := Derived.storageLive_owner_provenance copied_checked.1 copied_checked.2.1 opened_step 0 copied_checked.2.2
  have valid := (checked_assignment openedSpec.valid openedSpec.wellFormed word_step).1
  have fresh := Derived.assign_owner_provenance (bound := preparedWorld.memory.length) openedSpec.valid
    (by intro op member place same
        have selected : op = .move (.field (.local 0) none 0) := by simpa [ExpressionSourcesAbove, OperandSourcesAbove, wordExpr] using member
        have pathEq := SourceEval.Operand.move.inj (same.symm.trans selected)
        cases pathEq
        exact firstFresh) word_step
  let masks := wordActive.state.set 4 (.node .word 1 [.boxed .empty, .boxed (Slot.ofValue (encodeWord .Empty))])
  have moved : operand wordWorld wordActive.roots [] wordActive.state
      (.move (.deref (.field (.local 4) (some 1) 0))) = some ((.node .word 0 [], encodeWord .Empty), masks) := by with_unfolding_all rfl
  exact ⟨masks, moved, (operand_owner_provenance valid moved).1 4 fresh, by with_unfolding_all rfl⟩

private theorem base_resources : OwnerFrame base [0, 1, 2, 3] ∧ BoxCoverage base [0, 1, 2, 3] := by
  refine ⟨⟨by decide +kernel, ?_, ?_⟩, ?_⟩
  · intro address member
    have bound : address < 4 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [base, bound]
  · intro address member
    have bound : address < 4 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [base, bound]
  · intro address classified _
    have bound : address < 4 := by simpa [base] using classified
    simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
private def rightQuery : Cell := .shared ⟨2, [2, 0]⟩
private theorem right_query_readable : Readable base.memory base.live rightQuery (.reference (encodeWord (.Pair .Empty .Empty))) :=
  ⟨[0, 1, 2], .shared rfl (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil))), by simp [AliveOn, base]⟩

-- Complete empty-query miss execution retains arbitrary typed warm table data
-- and table-owned aliases, with a fresh returned witness field after closure.
example : ∃ fuel budget final packet lookupCost insertCost,
    packet.2 = SourceEval.Evaluator.encodeOutput (some SourceEval.Evaluator.emptyWitness)
      (.Entry ⟨.Empty, .Pair .Empty .Empty, SourceEval.Evaluator.emptyWitness⟩ table) ∧
    ResultOwnersAbove base.memory.length final.memory packet.1 ∧
    ∀ largerFuel largerBudget, fuel ≤ largerFuel → budget ≤ largerBudget →
      Recursive.original largerBudget largerFuel base [] [] .evaluate
        (SourceEval.Evaluator.inputPackets query rightQuery tableCell .Empty (.Pair .Empty .Empty) table) =
        some (final, packet, SourceEval.Evaluator.emptyRunCost .Empty lookupCost insertCost) := by
  have tableFoot := table_graph.footprint (Borrow.typed_unborrowed (table_graph.represents.typed (table_typed table)) (.adt .table))
  have input : FieldsFootprint base.memory [query, rightQuery, tableCell] [0, 1, 2, 3] :=
    .cons (.shared _) (.cons (.shared _) (.cons tableFoot .nil))
  obtain ⟨fuel, budget, final, packet, lookupCost, insertCost, value, _, _, _, _, _, _, _, fresh, stable⟩ :=
    SourceEval.Evaluator.empty_miss_total_fresh (guards := []) (external := []) base_valid (by simp) Callers.nil .Empty (.Pair .Empty .Empty) table
      query rightQuery tableCell (packets_readable (query, .reference (encodeWord .Empty)) (by simp [packets]))
      right_query_readable ⟨[0, 1, 2, 3], table_graph, by simp [AliveOn, base]⟩ input
      (by simpa [callerOwners] using base_resources.1) (by simpa [callerOwners] using base_resources.2)
      (by simp) (Or.inl rfl) (by simp [table, MemoizedOrderedSolver.findResult])
  exact ⟨fuel, budget, final, packet, lookupCost, insertCost, value, fresh, stable⟩

end SourceOwnerProvenanceTests
