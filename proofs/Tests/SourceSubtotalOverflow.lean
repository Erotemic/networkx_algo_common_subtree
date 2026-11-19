import SubtreeProofs.Rust.SourceSubtotalOverflowTotality
import SubtreeProofs.Rust.SourceEmptyOwnerProvenance

namespace SourceSubtotalOverflowTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage
open SourceEval.Addressed verified_ordered_core

-- Both parent query references borrow the nonempty witness inside the old
-- table. Each recursive hit copies its two owned word children. The overflowing
-- parent must drop both copies and return the original four-owner table.
private def word : BalancedWord := .Pair .Empty .Empty
private def witness : CommonEmbedding := ⟨word, 4294967295#u32⟩
private def table : MemoTable := .Entry ⟨.Empty, .Empty, witness⟩ .Empty
private def entry : Cell := .node .entry 0 [.node .word 0 [], .node .word 0 [],
  .node .embedding 0 [.node .word 1 [.owned 0, .owned 1], .number 4294967295]]
private def world : World := ⟨[.node .word 0 [], .node .word 0 [], entry, .node .table 0 []],
  fun address => if address < 4 then some .box else none, fun address => decide (address < 4)⟩
private def tableCell : Cell := .node .table 1 [.owned 2, .owned 3]
private def queryCell : Cell := .shared ⟨2, [2, 0]⟩

private theorem entry_graph : Graph world.memory entry
    (.node .entry 0 [encodeWord .Empty, encodeWord .Empty, encodeResult witness]) [0, 1] :=
  .node (.cons (.node .nil) (.cons (.node .nil) (.cons
    (.node (.cons (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))
      (.cons (.number _) .nil))) .nil)))

private theorem entry_footprint : Footprint world.memory entry [0, 1] :=
  .node (.cons (.node .nil) (.cons (.node .nil) (.cons
    (.node (.cons (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))
      (.cons (.number _) .nil))) .nil)))

private theorem table_footprint : Footprint world.memory tableCell [0, 1, 2, 3] :=
  .node (.cons (.owned rfl entry_footprint) (.cons (.owned rfl (.node .nil)) .nil))

private theorem table_readable : Readable world.memory world.live tableCell (encodeTable table) :=
  ⟨[0, 1, 2, 3], .node (.cons (.owned rfl entry_graph) (.cons (.owned rfl (.node .nil)) .nil)),
    by simp [AliveOn, world]⟩

private theorem query_readable : Readable world.memory world.live queryCell (.reference (encodeWord word)) :=
  ⟨[0, 1, 2], .shared rfl (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil))),
    by simp [AliveOn, world]⟩

private theorem resources : OwnerFrame world [0, 1, 2, 3] ∧ BoxCoverage world [0, 1, 2, 3] := by
  refine ⟨⟨by decide +kernel, ?_, ?_⟩, ?_⟩
  · intro address member
    have bound : address < 4 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [world, bound]
  · intro address member
    have bound : address < 4 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [world, bound]
  · intro address classified _
    have bound : address < 4 := by simpa [world] using classified
    simp only [List.mem_cons, List.not_mem_nil, or_false]; omega

example : ∃ fuel budget final packet cost owners,
    packet.2 = SourceEval.Evaluator.encodeOutput none table ∧
    Readable final.memory final.live packet.1 packet.2 ∧
    Footprint final.memory packet.1 owners ∧ owners.length = 4 ∧
    OwnerFrame final owners ∧ BoxCoverage final owners ∧
    ResultOwnersAbove world.memory.length final.memory packet.1 ∧
    SourceEval.Evaluator.Evaluation fuel word word table none table cost ∧
    ∀ largerFuel largerBudget, fuel ≤ largerFuel → budget ≤ largerBudget →
      Recursive.original largerBudget largerFuel world [] [] .evaluate
        (SourceEval.Evaluator.inputPackets queryCell queryCell tableCell word word table) = some (final, packet, cost) := by
  have input : FieldsFootprint world.memory [queryCell, queryCell, tableCell] [0, 1, 2, 3] :=
    .cons (.shared _) (.cons (.shared _) (.cons table_footprint .nil))
  have hit := SourceEval.Evaluator.cache_hit_native table .Empty .Empty witness
    (by simp [table, MemoizedOrderedSolver.findResult])
  obtain ⟨fuel, budget, final, packet, cost, value, readable, _, _, owned, evaluation, fresh, stable⟩ :=
    SourceEval.Evaluator.subtotal_overflow_total_fresh (external := [])
      (by simp [World.WellFormed, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty table table table witness witness queryCell queryCell tableCell
      query_readable query_readable table_readable input
      (by simpa [callerOwners] using resources.1) (by simpa [callerOwners] using resources.2)
      (guards := []) (by simp) (by simp [table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total_fresh .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total_fresh .Empty .Empty (Or.inl rfl)) hit hit (by decide +kernel)
  obtain ⟨owners, footprint, frame, covered⟩ := owned
  have readCopy := readable
  obtain ⟨used, graph, _⟩ := readCopy
  have count := (Rep.of_full graph.represents footprint).boxes
  rw [value] at count
  exact ⟨fuel, budget, final, packet, cost, owners, value, readable, footprint, count.trans (by with_unfolding_all rfl),
    by simpa [callerOwners] using frame, by simpa [callerOwners] using covered, fresh, evaluation, stable⟩

end SourceSubtotalOverflowTests
