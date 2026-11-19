import SubtreeProofs.Rust.SourceMaximumTotality

namespace SourceMaximumTotalityTests

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

example : ∃ fuel budget final packet witness cost owners,
    packet.2 = encodeOption (some witness) ∧
    SubtreeProofs.Paper2004.OrderedTree.IsMaximumCommon
      (SubtreeProofs.Paper2004.OrderedTree.decodeDyck (OrderedSolver.toDyck witness.word))
      (SubtreeProofs.Paper2004.OrderedTree.decodeDyck (OrderedSolver.toDyck query))
      (SubtreeProofs.Paper2004.OrderedTree.decodeDyck (OrderedSolver.toDyck query)) ∧
    witness.edges.val = (SubtreeProofs.Paper2004.OrderedTree.decodeDyck (OrderedSolver.toDyck witness.word)).edgeCount ∧
    Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧
    Footprint final.memory packet.1 owners ∧ OwnerFrame final (owners ++ external) ∧
    BoxCoverage final (owners ++ external) ∧ (∀ address ∈ owners, 9 ≤ address) ∧
    ∀ largerFuel largerBudget, fuel ≤ largerFuel → budget ≤ largerBudget →
      Recursive.original largerBudget largerFuel world [] [] .maximum
        (SourceEval.Maximum.inputPackets queryCell queryCell query query) = some (final, packet, cost) ∧
      SourceEval.run SourceEval.Certificate.original.body largerFuel .maximum
        [.reference (encodeWord query), .reference (encodeWord query)] = some (packet.2, cost) := by
  obtain ⟨fuel, budget, final, packet, witness, cost, owners, value, _, maximum, score, _, readable,
    wf, _, footprint, frame, coverage, fresh, stable⟩ :=
    SourceEval.Maximum.native_maximum_total_correct (external := external) wf (by simp) Callers.nil
      query query queryCell queryCell readable readable
      (by simpa [callerOwners] using resources.1) (by simpa [callerOwners] using resources.2)
      (guards := []) (by simp) (by decide +kernel) (by decide +kernel)
  exact ⟨fuel, budget, final, packet, witness, cost, owners, value, maximum, score, readable, wf,
    footprint, by simpa [callerOwners] using frame, by simpa [callerOwners] using coverage, fresh, stable⟩

end SourceMaximumTotalityTests
