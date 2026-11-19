import SubtreeProofs.Rust.SourceUniversalEvaluatorTotality

namespace SourceUniversalFreshTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage
open SourceEval.Addressed verified_ordered_core

private def word : BalancedWord := .Pair .Empty .Empty
private def query : BalancedWord := .Pair word word
private def external : List Nat := [0, 1, 2, 3, 4, 5, 6]
private def world : World := ⟨[.node .word 0 [], .node .word 0 [], .node .word 1 [.owned 0, .owned 1],
    .node .word 0 [], .node .word 0 [], .node .word 1 [.owned 3, .owned 4],
    .node .word 1 [.owned 2, .owned 5]],
  fun address => if address < 7 then some .box else none, fun address => decide (address < 7)⟩
private def queryCell : Cell := .shared ⟨6, []⟩
private def tableCell : Cell := .node .table 0 []

private theorem query_readable : Readable world.memory world.live queryCell (.reference (encodeWord query)) :=
  ⟨external, .shared rfl (.node (.cons (.owned rfl
    (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))) (.cons (.owned rfl
    (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))) .nil))),
    by simp [AliveOn, world, external]⟩

private theorem table_readable : Readable world.memory world.live tableCell (encodeTable .Empty) :=
  ⟨[], .node .nil, by simp [AliveOn]⟩

private theorem resources : OwnerFrame world external ∧ BoxCoverage world external := by
  refine ⟨⟨by decide +kernel, ?_, ?_⟩, ?_⟩
  · intro address member
    have bound : address < 7 := by simp only [external, List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [world, bound]
  · intro address member
    have bound : address < 7 := by simp only [external, List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [world, bound]
  · intro address classified _
    have bound : address < 7 := by simpa [world] using classified
    simp only [external, List.mem_cons, List.not_mem_nil, or_false]; omega

-- Both references alias one old seven-owner query. Cold three-edge evaluation
-- needs the general induction, not the previous one-edge instance or supplied
-- smaller calling contracts. Independent sound-cache/width hypotheses establish
-- the mathematical witness while the actual source run keeps full resources.
example : ∃ fuel budget final packet witness output cost outputOwners,
    packet.2 = SourceEval.Evaluator.encodeOutput (some witness) output ∧
    MemoizedOrderedSolver.Consistent query query witness ∧ MemoizedOrderedSolver.TableSound output ∧
    SourceEval.Evaluator.Evaluation fuel query query .Empty (some witness) output cost ∧
    Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧
    Footprint final.memory packet.1 outputOwners ∧
    OwnerFrame final (outputOwners ++ external) ∧ BoxCoverage final (outputOwners ++ external) ∧
    ResultOwnersAbove world.memory.length final.memory packet.1 ∧
    ∀ largerFuel largerBudget, fuel ≤ largerFuel → budget ≤ largerBudget →
      SourceEval.Evaluator.Evaluation largerFuel query query .Empty (some witness) output cost ∧
      Recursive.original largerBudget largerFuel world [] [] .evaluate
        (SourceEval.Evaluator.inputPackets queryCell queryCell tableCell query query .Empty) = some (final, packet, cost) := by
  have input : FieldsFootprint world.memory [queryCell, queryCell, tableCell] [] :=
    .cons (.shared _) (.cons (.shared _) (.cons (.node .nil) .nil))
  obtain ⟨fuel, budget, final, packet, witness, output, cost, value, _, evaluated, consistent, sound,
    readable, wf, _, owned, fresh, stable⟩ :=
    SourceEval.Evaluator.native_evaluate_total_consistent (external := external)
      (by simp [World.WellFormed, world]) (by simp) Callers.nil query query .Empty queryCell queryCell tableCell
      query_readable query_readable table_readable input
      (by simpa [callerOwners] using resources.1) (by simpa [callerOwners] using resources.2)
      (guards := []) (by simp) trivial (by decide +kernel) (by decide +kernel)
  obtain ⟨outputOwners, footprint, frame, covered⟩ := owned
  exact ⟨fuel, budget, final, packet, witness, output, cost, outputOwners, value, consistent, sound, evaluated, readable, wf,
    footprint, by simpa [callerOwners] using frame, by simpa [callerOwners] using covered, fresh,
    fun largerFuel largerBudget fuelBound budgetBound =>
      ⟨evaluated.extend fuelBound, stable largerFuel largerBudget fuelBound budgetBound⟩⟩

end SourceUniversalFreshTests
