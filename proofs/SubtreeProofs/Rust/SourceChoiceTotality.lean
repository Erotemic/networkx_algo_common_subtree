module

public import SubtreeProofs.Rust.SourceChoiceBodyForward
public import SubtreeProofs.Rust.SourceOwnerInvoke
public import SubtreeProofs.Rust.SourceEvalTypedRecursive

/-! Actual parsed choice entry, whole-body execution and checked closure are
constructed for arbitrary native owned inputs. Sufficient transfer permission
separates their owners from suspended loans; suspended shared aliases otherwise
remain unrestricted. Fuel and ghost readback budgets may be arbitrary. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Choice

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem initial_closed (first second : CommonEmbedding) :
    ClosedState (initialState [encodeResult first, encodeResult second]) := by
  intro slot
  by_cases one : slot = 1
  · subst slot
    exact ⟨.adt .embedding, (by simpa [initialState, Partial.Locals.lift, initialEnv] using ofValue_typed (result_typed first)), .adt .embedding⟩
  · by_cases two : slot = 2
    · subst slot
      exact ⟨.adt .embedding, (by simpa [initialState, Partial.Locals.lift, initialEnv] using ofValue_typed (result_typed second)), .adt .embedding⟩
    · exact ⟨.u32, by rw [initial_empty first second one two]; exact .empty _, .u32⟩

theorem invoke_total (fuel budget : Nat) {world : World} {callers : List Activation} {guards : List Nat}
    (hw : world.WellFormed) (hc : ∀ a ∈ callers, a.Valid world)
    (first second : CommonEmbedding) (firstCell secondCell : Cell)
    (firstReadable : Readable world.memory world.live firstCell (encodeResult first))
    (secondReadable : Readable world.memory world.live secondCell (encodeResult second))
    {inputOwners external : List Nat} {previous : Resources} (view : Callers world callers previous)
    (input : FieldsFootprint world.memory [firstCell, secondCell] inputOwners)
    (frame : OwnerFrame world (inputOwners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (inputOwners ++ (callerOwners world callers ++ external)))
    (transfer : List.Disjoint inputOwners previous.loans) (protectedReads : guards ⊆ previous.reads) :
    ∃ final packet,
      Calling.guardedInvoke (Helpers.callee fuel budget) callers guards CallingCertificate.originalChoice world
        [(firstCell, encodeResult first), (secondCell, encodeResult second)] = some (final, packet, cost first second) ∧
      packet.2 = encodeResult (OrderedSolver.selectResult first second) ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧ Preserves world final guards ∧
      ∃ output, Footprint final.memory packet.1 output ∧
        OwnerFrame final (output ++ (callerOwners final callers ++ external)) ∧
        BoxCoverage final (output ++ (callerOwners final callers ++ external)) := by
  let packets : List ValueCell := [(firstCell, encodeResult first), (secondCell, encodeResult second)]
  let entered := world.stackCells world.memory.length (packets.map Prod.fst)
  let active := initialActivation world world.memory.length 6 packets
  have readable : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2 := by
    intro p member
    simp only [packets, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact firstReadable
    · exact secondReadable
  have bound : packets.length + 1 ≤ 6 := by simp [packets]
  obtain ⟨entryRun, valid, wellFormed, _⟩ := enter_complete hw world.memory.length 6 readable bound
  have kept := (world.stackCells_keeps hw world.memory.length (packets.map Prod.fst) previous.reads).preserves
  have own := enter_owner_resources hw world.memory.length 6 hc readable input frame covered entryRun
  have owned : active.owners entered = inputOwners := by
    rw [initialActivation_owners _ _ readable bound, packetOwners_unique readable input]
  have machine : ClosedMachine world callers previous external entered active := by
    refine ⟨hw, view, kept, valid, wellFormed, initialActivation_rootsSeparate hc _ _ _, ?_, ?_,
      initial_closed first second, own.1, own.2, ?_⟩
    · simp only [entered, World.stackCells, List.length_append]; omega
    · intro slot binding hb
      simp only [active, initialActivation, argumentRoots] at hb
      split at hb
      next => cases hb; change world.memory.length ≤ world.memory.length + (slot - 1); omega
      next => cases hb
    · rw [owned]; exact transfer
  obtain ⟨middle, after, cell, work, bodyRun, empty, fresh, separate⟩ := body_complete machine (Helpers.callee fuel budget)
    rfl first second rfl
    (by simp [active, initialActivation, argumentRoots]) (by simp [active, initialActivation, argumentRoots, packets])
    (by simp [active, initialActivation, argumentRoots, packets]) (by simp [active, initialActivation, argumentRoots, packets])
    (firstRoot := ⟨world.memory.length, world.memory.length⟩)
    (secondRoot := ⟨world.memory.length + 1, world.memory.length + 1⟩)
    (by simp [active, initialActivation, argumentRoots, packets]) (by simp [active, initialActivation, argumentRoots, packets])
  let packet : ValueCell := (cell, encodeResult (OrderedSolver.selectResult first second))
  have respects := Helpers.callee_typed_respects fuel budget
  have ready := Calling.readyFor_noCalls (Helpers.callee fuel budget) Derived.TypedReady callers body (by decide +kernel) entered active
  have flow := (Calling.exec_spec respects machine.valid machine.callersValid machine.wellFormed body ready bodyRun).2.2.2
  obtain ⟨owners, footprint, finalFrame, finalCovered⟩ := Calling.exec_owner_resources respects (Helpers.callee_owns fuel budget)
    machine.valid machine.callersValid machine.wellFormed body ready machine.ownerFrame machine.coverage bodyRun
  have bodyKept := Calling.exec_preserves respects machine.valid machine.callersValid machine.wellFormed body ready bodyRun
    (view.transport kept).scan
  have allKept : Preserves world middle previous.reads := kept.trans bodyKept
  obtain ⟨final, closeRun, _, _, finalWellFormed, finalReadable, closeKept, _, finalFootprint, outputFrame, outputCovered⟩ :=
    close_total (packet := packet) (guards := guards) (external := external)
      flow.active flow.callers flow.wellFormed separate
      (fun slot => by change (after.state slot).dropWork.boxes = 0; rw [empty slot]; simp only [Slot.dropWork]) flow.packet (result_typed _) (.adt .embedding)
      footprint finalFrame finalCovered
      (by
        intro suspended current
        have same := current.unique (view.transport allKept)
        rw [same]
        exact protectedReads)
      (by
        intro slot binding hb suspended current borrowed
        have old := view.preserved_read_bound hw allKept current binding.address (current.loans_subset_reads borrowed)
        have new := fresh slot binding hb
        omega)
  change close middle after callers guards packet = some final at closeRun
  have invokeRun : Calling.invoke (Helpers.callee fuel budget) callers guards CallingCertificate.originalChoice world packets =
      some (final, packet, (Cost.entry .chooseLonger).plus work) := by
    simp only [Calling.invoke, CallingCertificate.originalChoice_spec.1, CallingCertificate.originalChoice_spec.2.1,
      CallingCertificate.originalChoice_spec.2.2, packets, Types.inputs, List.length_cons, List.length_nil,
      Nat.reduceAdd, ite_true]
    change (do
      let (entered, active) ← enter world world.memory.length 6 packets
      let (flow, work) ← Calling.exec (Helpers.callee fuel budget) callers body entered active
      match flow with
      | .next _ _ => none
      | .returned middle after packet => do
        let final ← close middle after callers guards packet
        some (final, packet, (Cost.entry .chooseLonger).plus work)) = _
    rw [entryRun]
    simp only [bind, Option.bind]
    change (do
      let (flow, work) ← Calling.exec (Helpers.callee fuel budget) callers body entered active
      match flow with
      | .next _ _ => none
      | .returned middle after packet => do
        let final ← close middle after callers guards packet
        some (final, packet, (Cost.entry .chooseLonger).plus work)) = _
    rw [bodyRun]
    simp only [bind, Option.bind]
    change (do let final ← close middle after callers guards packet; some (final, packet, (Cost.entry .chooseLonger).plus work)) = _
    rw [closeRun]
    rfl
  have native := invoking_refines fuel budget CallingCertificate.originalChoice CallingCertificate.originalChoice_spec.1
    CallingCertificate.originalChoice_spec.2.2 hw hc readable first second rfl invokeRun
  have guarded := Calling.guardedInvoke_complete (callee := Helpers.callee fuel budget)
    (decl := CallingCertificate.originalChoice) (packets := packets) view.scan protectedReads
  refine ⟨final, packet, ?_, rfl, finalReadable, finalWellFormed,
    (allKept.weaken protectedReads).trans closeKept, owners, finalFootprint, outputFrame, outputCovered⟩
  rw [guarded, ← native.2.1]
  exact invokeRun

end SubtreeProofs.Rust.SourceEval.Choice
