module

public import SubtreeProofs.Rust.SourceEvalChoice
public import SubtreeProofs.Rust.SourceEvalChoiceCertificate

/-! Actual-source/native score choice, including live losing-value destruction
and its structural work. This proves snapshot execution and declared drop work;
addressed deallocation and evaluator-wide safety remain separate obligations. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Choice

open LookupSource LookupSource.Partial verified_ordered_core

theorem source_run (fuel : Nat) (first second : CommonEmbedding) :
    run Certificate.original.body (fuel + 1) .chooseLonger [encodeResult first, encodeResult second] =
      some (encodeResult (OrderedSolver.selectResult first second), cost first second) :=
  run_body Certificate.original.body actual_body fuel first second

theorem source_execute (fuel : Nat) (first second : CommonEmbedding) :
    Certificate.executeSource Input.Program.source 512 (fuel + 1) .chooseLonger
      [encodeResult first, encodeResult second] =
      .ok (some (encodeResult (OrderedSolver.selectResult first second), cost first second)) := by
  rw [Certificate.original_execute, source_run]

theorem source_native (fuel : Nat) (first second : CommonEmbedding) :
    ∃ result, verified_ordered_core.choose_longer first second = .ok result ∧
      run Certificate.original.body (fuel + 1) .chooseLonger [encodeResult first, encodeResult second] =
        some (encodeResult result, cost first second) :=
  ⟨_, OrderedSolver.choose_longer_correct first second, source_run fuel first second⟩

theorem first_on_tie (fuel : Nat) (first second : CommonEmbedding) (he : first.edges = second.edges) :
    run Certificate.original.body (fuel + 1) .chooseLonger [encodeResult first, encodeResult second] =
      some (encodeResult first, cost first second) ∧
    destroyed first second = (Slot.ofValue (encodeResult second)).dropWork := by
  constructor
  · simpa only [OrderedSolver.selectResult, he, lt_self_iff_false, ite_false] using source_run fuel first second
  · simp only [destroyed, loser, he, lt_self_iff_false, ite_false]

end SubtreeProofs.Rust.SourceEval.Choice
