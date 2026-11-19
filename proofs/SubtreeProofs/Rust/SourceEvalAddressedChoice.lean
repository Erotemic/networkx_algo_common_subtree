module

public import SubtreeProofs.Rust.SourceEvalAddressedControl
public import SubtreeProofs.Rust.SourceActivationInitial
public import SubtreeProofs.Rust.SourceEvalChoiceCertificate
public import SubtreeProofs.Rust.SourceEvalChoice

/-! The concrete addressed executor consumes the already checked actual choice
body and independent native tie rule. This is correspondence for successful
physical executions; universal physical check success and function teardown
remain distinct from the completed snapshot/native functional theorem. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Choice

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed Storage
open SourceEval.Addressed SourceEval.Addressed.Derived verified_ordered_core

theorem addressed_refines {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (first second : CommonEmbedding)
    (hi : active.state = initialState [encodeResult first, encodeResult second])
    {result : Flow} {work : SourceEval.Cost}
    (h : Derived.exec callers (Certificate.original.body .chooseLonger) world active = some (result, work)) :
    ∃ final after cell, result = .returned final after (cell, encodeResult (OrderedSolver.selectResult first second)) ∧
      work = ⟨⟨26 + (destroyed first second).visits, {}⟩, destroyed first second, 0⟩ ∧
      Readable final.memory final.live cell (encodeResult (OrderedSolver.selectResult first second)) ∧
      after.Valid final ∧ (∀ a ∈ callers, a.Valid final) ∧ final.WellFormed ∧
      after.frame = active.frame ∧ after.count = active.count := by
  obtain ⟨hs, hf, hn, hv⟩ := Derived.exec_spec (fun _ _ => none) ha hc hw _ h
  rw [actual_body, hi, body_exec] at hs
  have he := Option.some.inj hs
  obtain ⟨hout, hcost⟩ := Prod.mk.inj he
  cases result with
  | next _ _ => cases hout
  | returned final after packet =>
    rcases packet with ⟨cell, value⟩
    simp only [Flow.snapshot, SourceEval.Outcome.returned.injEq] at hout
    subst value
    exact ⟨final, after, cell, rfl, hcost.symm, hv.packet, hv.active, hv.callers, hv.wellFormed, hf, hn⟩

end SubtreeProofs.Rust.SourceEval.Choice
