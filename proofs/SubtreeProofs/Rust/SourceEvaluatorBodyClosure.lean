module

public import SubtreeProofs.Rust.SourceCloseTotality
public import SubtreeProofs.Rust.SourceOwnerRecursive
public import SubtreeProofs.Rust.SourceRecursiveBudget
public import SubtreeProofs.Rust.SourceEvaluatorNativeTotal

/-! Close a constructed native evaluator body and lift it into the actual
recursive dispatcher. Complete ownership, source/native agreement and a stable
final world/packet/full cost are derived from the real entry/body/return proof. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem evaluator_body_close_total {world entered middle : World} {active after : Activation} {callers : List Activation}
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
    (native : memoized_common_embedding left right table = .ok (result, output)) :
    ∃ final packet,
      packet.2 = encodeOutput result output ∧ Readable final.memory final.live packet.1 packet.2 ∧
      final.WellFormed ∧ Preserves world final guards ∧
      (∃ outputOwners, Footprint final.memory packet.1 outputOwners ∧
        OwnerFrame final (outputOwners ++ (callerOwners final callers ++ external)) ∧
        BoxCoverage final (outputOwners ++ (callerOwners final callers ++ external))) ∧
      Evaluation (fuel + 1) left right table result output ((Cost.entry .evaluate).plus work) ∧
      ∀ largerFuel largerBudget, fuel + 1 ≤ largerFuel → budget ≤ largerBudget →
        Recursive.original largerBudget largerFuel world guards callers .evaluate (inputPackets leftCell rightCell tableCell left right table) =
          some (final, packet, (Cost.entry .evaluate).plus work) := by
  let packets := inputPackets leftCell rightCell tableCell left right table
  have typed : SnapshotFieldsTyped [.reference (encodeWord left), .reference (encodeWord right), encodeTable table]
      (Types.inputs CallingCertificate.originalEvaluator.source.function) := by
    rw [CallingCertificate.originalEvaluator_spec.1]
    exact .cons (.shared (word_typed left)) (.cons (.shared (word_typed right)) (.cons (table_typed table) .nil))
  have locals : LocalsTyped CallingCertificate.originalEvaluator.locals active.state := by
    rw [state]
    exact Types.initial_typed typed CallingCertificate.originalEvaluator.boundary
  have respects := Recursive.original_typed_respects budget fuel
  have constraints := CallingCertificate.originalEvaluator.constraints
  rw [CallingCertificate.originalEvaluator_spec.2.2] at constraints
  have ready := Calling.readyFor_typed respects (Types.original_run_typed fuel) constraints
    machine.valid machine.callersValid machine.wellFormed locals
  have checked := Calling.exec_spec respects machine.valid machine.callersValid machine.wellFormed body ready bodyRun
  have flow := checked.2.2.2
  obtain ⟨owners, footprint, finalFrame, finalCovered⟩ := Calling.exec_owner_resources respects (Recursive.original_owns budget fuel)
    machine.valid machine.callersValid machine.wellFormed body ready machine.ownerFrame machine.coverage bodyRun
  let packet : ValueCell := (cell, encodeOutput result output)
  obtain ⟨final, closeRun, _, _, finalWellFormed, finalReadable, closeKept, retired, finalFootprint, outputFrame, outputCovered⟩ :=
    close_total (packet := packet) (guards := guards) (external := external)
      flow.active flow.callers flow.wellFormed separate
      (fun slot => by change (after.state slot).dropWork.boxes = 0; rw [empty slot]; simp only [Slot.dropWork])
      flow.packet (encodeOutput_typed result output) (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil)))
      footprint finalFrame finalCovered
      (by intro suspended current; rw [current.unique (machine.previousCallers.transport kept)]; exact protectedReads)
      (by intro slot binding hb suspended current borrowed
          have old := machine.previousCallers.preserved_read_bound machine.beforeWellFormed kept current binding.address (current.loans_subset_reads borrowed)
          have new := fresh slot binding hb
          omega)
  change close middle after callers guards packet = some final at closeRun
  have invokeRun : Calling.invoke (Recursive.original budget fuel) callers guards CallingCertificate.originalEvaluator world packets =
      some (final, packet, (Cost.entry .evaluate).plus work) := by
    simp only [Calling.invoke, CallingCertificate.originalEvaluator_spec.1, CallingCertificate.originalEvaluator_spec.2.2,
      packets, inputPackets, Types.inputs, List.length_cons, List.length_nil, Nat.reduceAdd, ite_true]
    change (do
      let (entered, active) ← enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount packets
      let (flow, work) ← Calling.exec (Recursive.original budget fuel) callers body entered active
      match flow with
      | .next _ _ => none
      | .returned middle after packet => do
        let final ← close middle after callers guards packet
        some (final, packet, (Cost.entry .evaluate).plus work)) = _
    rw [entryRun]
    simp only [bind, Option.bind]
    rw [bodyRun]
    change (do let final ← close middle after callers guards packet
               some (final, packet, (Cost.entry .evaluate).plus work)) = _
    rw [closeRun]
    rfl
  have guarded := Calling.guardedInvoke_complete (callee := Recursive.original budget fuel)
    (decl := CallingCertificate.originalEvaluator) (packets := packets) machine.previousCallers.scan protectedReads
  have actual : Recursive.original budget (fuel + 1) world guards callers .evaluate packets =
      some (final, packet, (Cost.entry .evaluate).plus work) := by
    simp only [Recursive.original, Recursive.run, Recursive.interpreted, ite_true, CallingCertificate.evaluator_lookup, bind, Option.bind]
    change Calling.guardedInvoke (Recursive.original budget fuel) callers guards CallingCertificate.originalEvaluator world packets = _
    rw [guarded]
    exact invokeRun
  have sourceRun := source_of_exec fuel _ _ _ (by rw [← state]; exact checked.1)
  refine ⟨final, packet, rfl, finalReadable, finalWellFormed, (kept.weaken protectedReads).trans closeKept,
    ⟨owners, finalFootprint, outputFrame, outputCovered⟩, ⟨sourceRun, native⟩, ?_⟩
  intro largerFuel largerBudget fuelBound budgetBound
  exact Recursive.original_enlarge fuelBound budgetBound actual

end SubtreeProofs.Rust.SourceEval.Evaluator
