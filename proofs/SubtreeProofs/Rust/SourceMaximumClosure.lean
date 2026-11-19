module

public import SubtreeProofs.Rust.SourceMaximumExecution
public import SubtreeProofs.Rust.SourceCloseTotality
public import SubtreeProofs.Rust.SourceOwnerRecursive
public import SubtreeProofs.Rust.SourceRecursiveBudget

/-! Close constructed public execution through the actual parsed declaration
and recursive dispatcher, retaining the complete source cost and owner ledger. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Maximum

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem source_of_exec (fuel : Nat) (args : List Value) (value : Value) (work : Cost)
    (he : SourceEval.exec (SourceEval.run Certificate.original.body fuel) body (initialState args) = some (.returned value, work)) :
    SourceEval.run Certificate.original.body (fuel + 1) .maximum args = some (value, (Cost.entry .maximum).plus work) := by
  rw [Legacy.run_ordinary Certificate.original.body fuel .maximum args (by decide) (by decide), actual_body, he]
  rfl

theorem body_close_total {world entered middle : World} {active after : Activation} {callers : List Activation}
    {previous : Resources} {guards external : List Nat} (left right : BalancedWord)
    (leftCell rightCell : Cell) (fuel budget : Nat) (cell : Cell) (work : Cost) (result : Option CommonEmbedding)
    (entryRun : enter world world.memory.length CallingCertificate.originalMaximum.source.localCount
      (inputPackets leftCell rightCell left right) = some (entered, active))
    (machine : LoanSafeMachine world callers previous external entered active)
    (state : active.state = initialState [.reference (encodeWord left), .reference (encodeWord right)])
    (bodyRun : Calling.exec (Recursive.original budget fuel) callers body entered active =
      some (.returned middle after (cell, encodeOption result), work))
    (empty : ∀ slot, after.state slot = .empty) (separate : after.RootsSeparate callers)
    (fresh : ∀ slot binding, after.roots slot = some binding → world.memory.length ≤ binding.address)
    (kept : Preserves world middle previous.reads) (protectedReads : guards ⊆ previous.reads) :
    ∃ final packet,
      packet.2 = encodeOption result ∧ Readable final.memory final.live packet.1 packet.2 ∧
      final.WellFormed ∧ Preserves world final guards ∧
      (∃ outputOwners, Footprint final.memory packet.1 outputOwners ∧
        OwnerFrame final (outputOwners ++ (callerOwners final callers ++ external)) ∧
        BoxCoverage final (outputOwners ++ (callerOwners final callers ++ external))) ∧
      SourceEval.run Certificate.original.body (fuel + 1) .maximum
        [.reference (encodeWord left), .reference (encodeWord right)] = some (packet.2, (Cost.entry .maximum).plus work) ∧
      ∀ largerFuel largerBudget, fuel + 1 ≤ largerFuel → budget ≤ largerBudget →
        Recursive.original largerBudget largerFuel world guards callers .maximum
          (inputPackets leftCell rightCell left right) = some (final, packet, (Cost.entry .maximum).plus work) := by
  let packets := inputPackets leftCell rightCell left right
  have typed : SnapshotFieldsTyped [.reference (encodeWord left), .reference (encodeWord right)]
      (Types.inputs CallingCertificate.originalMaximum.source.function) := by
    rw [CallingCertificate.originalMaximum_spec.1]
    exact .cons (.shared (word_typed left)) (.cons (.shared (word_typed right)) .nil)
  have locals : LocalsTyped CallingCertificate.originalMaximum.locals active.state := by
    rw [state]
    exact Types.initial_typed typed CallingCertificate.originalMaximum.boundary
  have respects := Recursive.original_typed_respects budget fuel
  have constraints := CallingCertificate.originalMaximum.constraints
  rw [CallingCertificate.originalMaximum_spec.2.2] at constraints
  have ready := Calling.readyFor_typed respects (Types.original_run_typed fuel) constraints
    machine.valid machine.callersValid machine.wellFormed locals
  have checked := Calling.exec_spec respects machine.valid machine.callersValid machine.wellFormed body ready bodyRun
  have flow := checked.2.2.2
  obtain ⟨owners, footprint, finalFrame, finalCovered⟩ := Calling.exec_owner_resources respects (Recursive.original_owns budget fuel)
    machine.valid machine.callersValid machine.wellFormed body ready machine.ownerFrame machine.coverage bodyRun
  let packet : ValueCell := (cell, encodeOption result)
  obtain ⟨final, closeRun, _, _, finalWf, finalRead, closeKept, _, finalFootprint, outputFrame, outputCovered⟩ :=
    close_total (packet := packet) (guards := guards) (external := external)
      flow.active flow.callers flow.wellFormed separate
      (fun slot => by change (after.state slot).dropWork.boxes = 0; rw [empty slot]; simp only [Slot.dropWork])
      flow.packet (option_typed result) (.adt .optional) footprint finalFrame finalCovered
      (by intro suspended current; rw [current.unique (machine.previousCallers.transport kept)]; exact protectedReads)
      (by intro slot binding hb suspended current borrowed
          have old := machine.previousCallers.preserved_read_bound machine.beforeWellFormed kept current binding.address
            (current.loans_subset_reads borrowed)
          have new := fresh slot binding hb
          omega)
  change close middle after callers guards packet = some final at closeRun
  have invokeRun : Calling.invoke (Recursive.original budget fuel) callers guards CallingCertificate.originalMaximum world packets =
      some (final, packet, (Cost.entry .maximum).plus work) := by
    simp only [Calling.invoke, CallingCertificate.originalMaximum_spec.1, CallingCertificate.originalMaximum_spec.2.2,
      packets, inputPackets, Types.inputs, List.length_cons, List.length_nil, Nat.reduceAdd, ite_true]
    change (do
      let (entered, active) ← enter world world.memory.length CallingCertificate.originalMaximum.source.localCount packets
      let (flow, work) ← Calling.exec (Recursive.original budget fuel) callers body entered active
      match flow with
      | .next _ _ => none
      | .returned middle after packet => do
        let final ← close middle after callers guards packet
        some (final, packet, (Cost.entry .maximum).plus work)) = _
    rw [entryRun]
    simp only [bind, Option.bind]
    rw [bodyRun]
    change (do let final ← close middle after callers guards packet
               some (final, packet, (Cost.entry .maximum).plus work)) = _
    rw [closeRun]
    rfl
  have guarded := Calling.guardedInvoke_complete (callee := Recursive.original budget fuel)
    (decl := CallingCertificate.originalMaximum) (packets := packets) machine.previousCallers.scan protectedReads
  have actual : Recursive.original budget (fuel + 1) world guards callers .maximum packets =
      some (final, packet, (Cost.entry .maximum).plus work) := by
    simp only [Recursive.original, Recursive.run, Recursive.interpreted, ite_true, CallingCertificate.maximum_lookup, bind, Option.bind]
    change Calling.guardedInvoke (Recursive.original budget fuel) callers guards CallingCertificate.originalMaximum world packets = _
    rw [guarded]
    exact invokeRun
  have sourceRun := source_of_exec fuel _ _ _ (by rw [← state]; exact checked.1)
  exact ⟨final, packet, rfl, finalRead, finalWf, (kept.weaken protectedReads).trans closeKept,
    ⟨owners, finalFootprint, outputFrame, outputCovered⟩, sourceRun,
    fun largerFuel largerBudget fuelBound budgetBound => Recursive.original_enlarge fuelBound budgetBound actual⟩

end SubtreeProofs.Rust.SourceEval.Maximum
