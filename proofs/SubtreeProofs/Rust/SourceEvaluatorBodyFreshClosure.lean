module

public import SubtreeProofs.Rust.SourceEvaluatorBodyClosure
public import SubtreeProofs.Rust.SourceInvokeReturnedPacket
public import SubtreeProofs.Rust.SourceResultOwnerProvenance

/-! The existing checked evaluator body closure also preserves a separately
proved witness-field owner bound. The returned packet is derived from invoke. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem evaluator_body_close_total_fresh {world entered middle : World} {active after : Activation} {callers : List Activation}
    {previous : Resources} {guards external : List Nat} (left right : BalancedWord) (table : MemoTable)
    (leftCell rightCell tableCell : Cell) (fuel budget : Nat) (cell : Cell) (work : Cost)
    (result : Option CommonEmbedding) (output : MemoTable)
    (entryRun : enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount
      (inputPackets leftCell rightCell tableCell left right table) = some (entered, active))
    (machine : LoanSafeMachine world callers previous external entered active)
    (state : active.state = initialState [.reference (encodeWord left), .reference (encodeWord right), encodeTable table])
    (bodyRun : Calling.exec (Recursive.original budget fuel) callers body entered active =
      some (.returned middle after (cell, encodeOutput result output), work))
    (empty : ∀ slot, after.state slot = .empty) (separate : after.RootsSeparate callers)
    (fresh : ∀ slot binding, after.roots slot = some binding → world.memory.length ≤ binding.address)
    (kept : Preserves world middle previous.reads) (protectedReads : guards ⊆ previous.reads)
    (native : memoized_common_embedding left right table = .ok (result, output))
    (resultFresh : ResultOwnersAbove world.memory.length middle.memory cell) :
    ∃ final packet,
      packet.2 = encodeOutput result output ∧ Readable final.memory final.live packet.1 packet.2 ∧
      final.WellFormed ∧ Preserves world final guards ∧
      (∃ outputOwners, Footprint final.memory packet.1 outputOwners ∧
        OwnerFrame final (outputOwners ++ (callerOwners final callers ++ external)) ∧
        BoxCoverage final (outputOwners ++ (callerOwners final callers ++ external))) ∧
      Evaluation (fuel + 1) left right table result output ((Cost.entry .evaluate).plus work) ∧
      ResultOwnersAbove world.memory.length final.memory packet.1 ∧
      ∀ largerFuel largerBudget, fuel + 1 ≤ largerFuel → budget ≤ largerBudget →
        Recursive.original largerBudget largerFuel world guards callers .evaluate (inputPackets leftCell rightCell tableCell left right table) =
          some (final, packet, (Cost.entry .evaluate).plus work) := by
  obtain ⟨final, packet, value, readable, wf, preserved, owned, evaluation, stable⟩ :=
    evaluator_body_close_total left right table leftCell rightCell tableCell fuel budget cell work result output
      entryRun machine state bodyRun empty separate fresh kept protectedReads native
  have actual := stable (fuel + 1) budget (by rfl) (by rfl)
  simp only [Recursive.original, Recursive.run, Recursive.interpreted, ite_true,
    CallingCertificate.evaluator_lookup, bind, Option.bind] at actual
  change Calling.guardedInvoke (Recursive.original budget fuel) callers guards CallingCertificate.originalEvaluator world
    (inputPackets leftCell rightCell tableCell left right table) = some (final, packet, (Cost.entry .evaluate).plus work) at actual
  rw [Calling.guardedInvoke_complete machine.previousCallers.scan protectedReads] at actual
  have declared : Calling.exec (Recursive.original budget fuel) callers CallingCertificate.originalEvaluator.source.code entered active =
      some (.returned middle after (cell, encodeOutput result output), work) := by
    rw [CallingCertificate.originalEvaluator_spec.2.2]; exact bodyRun
  obtain ⟨samePacket, closeRun, _⟩ := Calling.invoke_returned_close entryRun declared actual
  have memory := close_memory closeRun
  refine ⟨final, packet, value, readable, wf, preserved, owned, evaluation, ?_, stable⟩
  rw [samePacket, memory]
  exact resultFresh

end SubtreeProofs.Rust.SourceEval.Evaluator
