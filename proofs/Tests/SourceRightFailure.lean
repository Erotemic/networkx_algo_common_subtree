import SubtreeProofs.Rust.SourceRightFailureTotality
import SubtreeProofs.Rust.SourceMinimalPairTotality

namespace SourceRightFailureTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage
open SourceEval.Addressed verified_ordered_core

private def word : BalancedWord := .Pair .Empty .Empty
private def larger : BalancedWord := .Pair .Empty word
private def headWitness : CommonEmbedding := ⟨word, 2147483648#u32⟩
private def tailWitness : CommonEmbedding := ⟨word, 0#u32⟩
private def table : MemoTable := .Entry ⟨.Empty, .Empty, headWitness⟩
  (.Entry ⟨.Empty, word, tailWitness⟩ (.Entry ⟨.Empty, larger, tailWitness⟩ .Empty))
private def headEntry : Cell := .node .entry 0 [.node .word 0 [], .node .word 0 [],
  .node .embedding 0 [.node .word 1 [.owned 0, .owned 1], .number 2147483648]]
private def tailEntry : Cell := .node .entry 0 [.node .word 0 [], .node .word 1 [.owned 4, .owned 5],
  .node .embedding 0 [.node .word 1 [.owned 6, .owned 7], .number 0]]
private def leftEntry : Cell := .node .entry 0 [.node .word 0 [], .node .word 1 [.owned 10, .owned 11],
  .node .embedding 0 [.node .word 1 [.owned 15, .owned 16], .number 0]]
private def world : World := ⟨[.node .word 0 [], .node .word 0 [], headEntry, tailEntry,
    .node .word 0 [], .node .word 0 [], .node .word 0 [], .node .word 0 [], .node .table 0 [],
    .node .table 1 [.owned 3, .owned 17], .node .word 0 [], .node .word 1 [.owned 12, .owned 13],
    .node .word 0 [], .node .word 0 [], leftEntry, .node .word 0 [], .node .word 0 [],
    .node .table 1 [.owned 14, .owned 8]],
  fun address => if address < 18 then some .box else none, fun address => decide (address < 18)⟩
private def tableCell : Cell := .node .table 1 [.owned 2, .owned 9]
private def leftCell : Cell := .shared ⟨2, [2, 0]⟩
private def rightCell : Cell := .shared ⟨14, [1]⟩
private def owners : List Nat := [0, 1, 2, 4, 5, 6, 7, 3, 10, 12, 13, 11, 15, 16, 14, 8, 17, 9]

private theorem head_graph : Graph world.memory headEntry
    (.node .entry 0 [encodeWord .Empty, encodeWord .Empty, encodeResult headWitness]) [0, 1] :=
  .node (.cons (.node .nil) (.cons (.node .nil) (.cons
    (.node (.cons (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))
      (.cons (.number _) .nil))) .nil)))

private theorem tail_graph : Graph world.memory tailEntry
    (.node .entry 0 [encodeWord .Empty, encodeWord word, encodeResult tailWitness]) [4, 5, 6, 7] :=
  .node (.cons (.node .nil) (.cons
    (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil))) (.cons
    (.node (.cons (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))
      (.cons (.number _) .nil))) .nil)))

private theorem left_graph : Graph world.memory leftEntry
    (.node .entry 0 [encodeWord .Empty, encodeWord larger, encodeResult tailWitness]) [10, 12, 13, 11, 15, 16] :=
  .node (.cons (.node .nil) (.cons
    (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl
      (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))) .nil))) (.cons
    (.node (.cons (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))
      (.cons (.number _) .nil))) .nil)))

private theorem table_graph : Graph world.memory tableCell (encodeTable table) owners :=
  .node (.cons (.owned rfl head_graph) (.cons (.owned rfl
    (.node (.cons (.owned rfl tail_graph) (.cons (.owned rfl
      (.node (.cons (.owned rfl left_graph) (.cons (.owned rfl (.node .nil)) .nil)))) .nil)))) .nil))

private theorem table_footprint : Footprint world.memory tableCell owners :=
  table_graph.footprint (Borrow.typed_unborrowed (table_graph.represents.typed (table_typed table)) (.adt .table))

private theorem table_readable : Readable world.memory world.live tableCell (encodeTable table) :=
  ⟨owners, table_graph, by simp [AliveOn, world, owners]⟩

private theorem left_readable : Readable world.memory world.live leftCell (.reference (encodeWord word)) :=
  ⟨[0, 1, 2], .shared rfl (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil))),
    by simp [AliveOn, world]⟩

private theorem right_readable : Readable world.memory world.live rightCell (.reference (encodeWord larger)) :=
  ⟨[10, 12, 13, 11, 14], .shared rfl (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl
    (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))) .nil))),
    by simp [AliveOn, world]⟩

private theorem resources : OwnerFrame world owners ∧ BoxCoverage world owners := by
  refine ⟨⟨by decide +kernel, ?_, ?_⟩, ?_⟩
  · intro address member
    have bound : address < 18 := by simp only [owners, List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [world, bound]
  · intro address member
    have bound : address < 18 := by simp only [owners, List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [world, bound]
  · intro address classified _
    have bound : address < 18 := by simpa [world] using classified
    simp only [owners, List.mem_cons, List.not_mem_nil, or_false]; omega

-- All four smaller fresh contracts are proved instances. Both parent queries
-- borrow inside the owned table. Right failure retires a two-owner right query,
-- a two-owner left witness and the six-owner matched candidate.
example : ∃ fuel budget final packet cost outputOwners,
    packet.2 = SourceEval.Evaluator.encodeOutput none table ∧
    Readable final.memory final.live packet.1 packet.2 ∧
    Footprint final.memory packet.1 outputOwners ∧ outputOwners.length = 18 ∧
    OwnerFrame final outputOwners ∧ BoxCoverage final outputOwners ∧
    ResultOwnersAbove world.memory.length final.memory packet.1 ∧
    SourceEval.Evaluator.Evaluation fuel word larger table none table cost ∧
    ∀ largerFuel largerBudget, fuel ≤ largerFuel → budget ≤ largerBudget →
      Recursive.original largerBudget largerFuel world [] [] .evaluate
        (SourceEval.Evaluator.inputPackets leftCell rightCell tableCell word larger table) = some (final, packet, cost) := by
  have input : FieldsFootprint world.memory [leftCell, rightCell, tableCell] owners :=
    .cons (.shared _) (.cons (.shared _) (.cons table_footprint .nil))
  have headHit := SourceEval.Evaluator.cache_hit_native table .Empty .Empty headWitness
    (by simp [table, MemoizedOrderedSolver.findResult])
  have tailHit := SourceEval.Evaluator.cache_hit_native table .Empty word tailWitness
    (by simp [table, word, MemoizedOrderedSolver.findResult])
  have leftHit := SourceEval.Evaluator.cache_hit_native table .Empty larger tailWitness
    (by simp [table, word, larger, MemoizedOrderedSolver.findResult])
  have rightNone := SourceEval.Evaluator.subtotal_overflow_native table table table .Empty .Empty .Empty .Empty headWitness headWitness
    (by simp [table, word, larger, MemoizedOrderedSolver.findResult]) headHit headHit (by decide +kernel)
  obtain ⟨fuel, budget, final, packet, cost, value, readable, _, _, owned, evaluation, fresh, stable⟩ :=
    SourceEval.Evaluator.right_failure_total_fresh (external := [])
      (by simp [World.WellFormed, world]) (by simp) Callers.nil
      .Empty .Empty .Empty word table table table table headWitness tailWitness 2147483648#u32 2147483649#u32
      leftCell rightCell tableCell left_readable right_readable table_readable input
      (by simpa [callerOwners] using resources.1) (by simpa [callerOwners] using resources.2)
      (guards := []) (by simp) (by simp [table, word, larger, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total_fresh .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total_fresh .Empty word (Or.inl rfl)) headHit tailHit
      (by decide +kernel) (by decide +kernel)
      (SourceEval.Evaluator.native_empty_total_fresh .Empty larger (Or.inl rfl)) tailWitness table leftHit
      SourceEval.Evaluator.native_minimal_pair_total_fresh rightNone
  obtain ⟨outputOwners, footprint, frame, covered⟩ := owned
  have readCopy := readable
  obtain ⟨used, graph, _⟩ := readCopy
  have count := (Rep.of_full graph.represents footprint).boxes
  rw [value] at count
  exact ⟨fuel, budget, final, packet, cost, outputOwners, value, readable, footprint, count.trans (by with_unfolding_all rfl),
    by simpa [callerOwners] using frame, by simpa [callerOwners] using covered, fresh, evaluation, stable⟩

end SourceRightFailureTests
