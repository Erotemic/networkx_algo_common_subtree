import SubtreeProofs.Rust.SourceColdEvaluatorProvenance

namespace SourceColdProvenanceTests

open SubtreeProofs.Rust LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed
open verified_ordered_core

private def leaf : BalancedWord := .Pair .Empty .Empty
private def query : BalancedWord := .Pair leaf leaf
private def external : List Nat := [0, 1, 2, 3, 4, 5, 6]

-- The old heap includes an unrelated dead Box and a live scalar stack cell.
-- Both query references alias the same seven-owner tree.
private def world : World := ⟨[.node .word 0 [], .node .word 0 [], .node .word 1 [.owned 0, .owned 1],
    .node .word 0 [], .node .word 0 [], .node .word 1 [.owned 3, .owned 4],
    .node .word 1 [.owned 2, .owned 5], .number 23, .number 42],
  fun a => if a < 8 then some .box else if a = 8 then some (.stack 10 0 8) else none,
  fun a => decide (a < 7 ∨ a = 8)⟩
private def queryCell : Cell := .shared ⟨6, []⟩

private theorem readable : Readable world.memory world.live queryCell (.reference (encodeWord query)) :=
  ⟨external, .shared rfl (.node (.cons (.owned rfl
    (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))) (.cons (.owned rfl
    (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))) .nil))),
    by simp [AliveOn, world, external]⟩

private theorem resources : OwnerFrame world external ∧ BoxCoverage world external := by
  refine ⟨⟨by decide +kernel, ?_, ?_⟩, ?_⟩
  · intro a hm
    have bound : a < 7 := by simp only [external, List.mem_cons, List.not_mem_nil, or_false] at hm; omega
    simp [world, show a < 8 by omega]
  · intro a hm
    have bound : a < 7 := by simp only [external, List.mem_cons, List.not_mem_nil, or_false] at hm; omega
    simp [world, bound]
  · intro a hc hl
    have bound : a < 7 := by
      have live : a < 7 ∨ a = 8 := of_decide_eq_true hl
      rcases live with live | rfl
      · exact live
      · change some (Class.stack 10 0 8) = some .box at hc
        cases hc
    simp only [external, List.mem_cons, List.not_mem_nil, or_false]; omega

private theorem wf : world.WellFormed := by
  constructor
  · intro a
    change ((if a < 8 then some Class.box else if a = 8 then some (.stack 10 0 8) else none).isSome = true ↔ a < 9)
    split_ifs <;> simp_all <;> omega
  · intro a ha
    have := of_decide_eq_true ha
    change a < 9
    omega

example : ∃ fuel budget final packet result output cost owners,
    packet.2 = SourceEval.Evaluator.encodeOutput result output ∧
    SourceEval.Evaluator.Evaluation fuel query query .Empty result output cost ∧
    Footprint final.memory packet.1 owners ∧ OwnerFrame final (owners ++ external) ∧
    BoxCoverage final (owners ++ external) ∧ (∀ address ∈ owners, 9 ≤ address) ∧
    ∀ largerFuel largerBudget, fuel ≤ largerFuel → budget ≤ largerBudget →
      Recursive.original largerBudget largerFuel world [] [] .evaluate
        (SourceEval.Evaluator.inputPackets queryCell queryCell (.node .table 0 []) query query .Empty) =
        some (final, packet, cost) := by
  obtain ⟨fuel, budget, final, packet, result, output, cost, owners, value, _, evaluated, _, _, _,
    footprint, frame, coverage, fresh, stable⟩ :=
    SourceEval.Evaluator.native_evaluate_cold_total (external := external) wf (by simp) Callers.nil
      query query queryCell queryCell readable readable
      (by simpa [callerOwners] using resources.1) (by simpa [callerOwners] using resources.2)
      (guards := []) (by simp)
  exact ⟨fuel, budget, final, packet, result, output, cost, owners, value, evaluated, footprint,
    by simpa [callerOwners] using frame, by simpa [callerOwners] using coverage, fresh, stable⟩

-- A relation that only preserved live input cells would permit resurrection.
-- The backward provenance contract rejects both relevant bad transitions.
example : ¬ BoxOrigin world { world with live := fun a => if a = 7 then true else world.live a } := by
  intro h
  have old := h.old 7 (by decide +kernel) (by rfl) (by rfl)
  have : false = true := old.2
  cases this

example : ¬ BoxOrigin world { world with classes := fun a => if a = 8 then some .box else world.classes a } := by
  intro h
  have old := h.old 8 (by decide +kernel) (by rfl) (by rfl)
  have : some (Class.stack 10 0 8) = some .box := old.1
  cases this

end SourceColdProvenanceTests
