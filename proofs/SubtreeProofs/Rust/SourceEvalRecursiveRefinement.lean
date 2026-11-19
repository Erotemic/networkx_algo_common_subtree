module

public import SubtreeProofs.Rust.SourceEvalRecursiveCalls
public import SubtreeProofs.Rust.SourceEvalTotal

/-! Recursive addressed execution reuses the completed independent native choice
and evaluator results, including arbitrary warm tables and overflow exits.
Caller bytes/liveness and complete source costs remain in the conclusion.
Evaluator path readiness and concrete success are explicit, not totality claims. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Recursive

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed Storage verified_ordered_core

theorem original_choice_refines (budget fuel : Nat) {world final : World} {callers : List Activation} {guards : List Nat}
    {packets : List ValueCell} {packet : ValueCell} {cost : Cost}
    (hw : world.WellFormed) (hc : ∀ a ∈ callers, a.Valid world)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2) (hl : AliveOn world.live guards)
    (first second : CommonEmbedding) (hi : packets.map Prod.snd = [encodeResult first, encodeResult second])
    (h : original budget (fuel + 1) world guards callers .chooseLonger packets = some (final, packet, cost)) :
    packet.2 = encodeResult (OrderedSolver.selectResult first second) ∧ cost = Choice.cost first second ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧ Preserves world final guards := by
  obtain ⟨hs, hr, hf, hk⟩ := original_respects budget (fuel + 1) world guards callers .chooseLonger packets final packet cost
    hw hp hc hl (ready_original_choice budget fuel world packets) h
  rw [hi, Choice.run_body Certificate.original.body Choice.actual_body] at hs
  obtain ⟨hv, he⟩ := Prod.mk.inj (Option.some.inj hs)
  exact ⟨hv.symm, he.symm, hr, hf, hk⟩

theorem original_evaluate_refines (budget fuel : Nat) {world final : World} {callers : List Activation} {guards : List Nat}
    {packets : List ValueCell} {packet : ValueCell} {cost : Cost}
    (hw : world.WellFormed) (hc : ∀ a ∈ callers, a.Valid world)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2) (hl : AliveOn world.live guards)
    (left right : BalancedWord) (table : MemoTable)
    (hi : packets.map Prod.snd = [.reference (encodeWord left), .reference (encodeWord right), encodeTable table])
    (hd : Ready CallingCertificate.originalProgram.definitions budget fuel world .evaluate packets)
    (h : original budget fuel world guards callers .evaluate packets = some (final, packet, cost)) :
    ∃ result output, packet.2 = Evaluator.encodeOutput result output ∧
      memoized_common_embedding left right table = .ok (result, output) ∧
      Evaluator.Evaluation fuel left right table result output cost ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧ Preserves world final guards := by
  obtain ⟨hs, hr, hf, hk⟩ := original_respects budget fuel world guards callers .evaluate packets final packet cost hw hp hc hl hd h
  rw [hi] at hs
  obtain ⟨result, output, he, evaluation⟩ := Evaluator.evaluate_refines left right table fuel hs
  exact ⟨result, output, he, evaluation.native, evaluation, hr, hf, hk⟩

end SubtreeProofs.Rust.SourceEval.Addressed.Recursive
