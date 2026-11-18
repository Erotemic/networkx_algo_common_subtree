module

public import SubtreeProofs.Rust.SourceOriginalBoxedWord
public import SubtreeProofs.Rust.SourceCallOwnerProvenance

/-! A boxed word retains its independently bounded payload owners and adds a
fresh shell. Untouched bounded locals survive the full actual five-step prefix. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem original_boxed_word_complete_fresh {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active)
    (source destination temporary : Nat) (sd : source ≠ destination) (st : source ≠ temporary) (dt : destination ≠ temporary)
    (sourceOutside : source ∉ exceptions) (outside : destination ∉ exceptions) (temporaryOutside : temporary ∉ exceptions)
    (bounded : ∀ index ∈ exceptions, index < active.count)
    (destinationBound : destination < active.count) (temporaryBound : temporary < active.count)
    (destinationUnbound : active.roots destination = none) (temporaryUnbound : active.roots temporary = none)
    (result : CommonEmbedding) (initialized : active.state source = Slot.ofValue (encodeResult result)) (sourceAbove : LocalOwnersAbove before.memory.length world active source) (suffix : Code) :
    ∃ minimumFuel minimumBudget final after,
      OriginalLoanMachine before callers previous external exceptions final after ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      after.state source = resultWordHole result.edges ∧ after.state destination = Slot.ofValue (.boxed (encodeWord result.word)) ∧
      after.roots temporary = none ∧
      (∃ binding, after.roots destination = some binding) ∧
      (∀ slot, slot ≠ destination → slot ≠ temporary → after.roots slot = active.roots slot) ∧
      (∀ slot, slot ≠ source → slot ≠ destination → slot ≠ temporary → ∀ ty,
        SlotTyped (active.state slot) ty → Borrow.Closed ty → after.state slot = active.state slot) ∧
      (∀ index binding, active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      LocalOwnersAbove before.memory.length final after destination ∧
      (∀ other, other < active.count → other ≠ source → other ≠ destination → other ≠ temporary →
        LocalOwnersAbove before.memory.length world active other → LocalOwnersAbove before.memory.length final after other) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers suffix (boxWordActions source destination temporary) world active final after := by
  obtain ⟨minimumFuel, minimumBudget, final, after, machine, countAfter, frameAfter, hole, boxed, temporaryGone,
    destinationRoot, rootsAfter, closedAfter, memoryAfter, stable⟩ :=
    original_boxed_word_complete h source destination temporary sd st dt sourceOutside outside temporaryOutside bounded
      destinationBound temporaryBound destinationUnbound temporaryUnbound result initialized suffix
  let fuel := max minimumFuel 1
  let budget := minimumBudget
  let code := boxWordCode source destination temporary suffix
  let callee := Recursive.original budget fuel
  have whole := stable fuel budget (Nat.le_max_left _ _) (by rfl)
  obtain ⟨wd, ad, opened, md, rootsD, countD, frameD, emptyD, rawD, memoryD⟩ :=
    original_open_local_complete h callee (code 1) outside destinationBound destinationUnbound
  have valueD : ad.state source = Slot.ofValue (encodeResult result) :=
    (opened.closed_local_same (index := source) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [initialized]; exact ofValue_typed (result_typed result)) (.adt .embedding) rfl
      (by simp [LocalPreservation.action, sd])).trans initialized
  obtain ⟨wp, ap, projected, mp, rootsP, countP, frameP, holeP, valueP, memoryP⟩ :=
    original_project_view_complete md callee (code 3) (source := source) (destination := temporary) (place := .field (.local source) none 0) sourceOutside temporaryOutside st
      rfl trivial (by rw [valueD]; exact result_word_take result) (resultWordHole_typed result.edges) (.adt .embedding)
      (word_typed result.word) (.adt .word) (by rw [countD]; exact temporaryBound)
      (by simpa [rootsD, Roots.set, Ne.symm dt] using temporaryUnbound)
  have first3 : Calling.Prefix callee callers (code 3) ((boxWordActions source destination temporary).take 3) world active wp ap :=
    Calling.Prefix.append (suffix := code 3) (rest := [.storageLive temporary, .assign temporary (.use (.move (.field (.local source) none 0)))]) opened projected
  have transfer : OwnerTransfer source ((boxWordActions source destination temporary).take 3) temporary := by
    refine .keep rfl ?_ (.keep rfl ?_ (.assign (fun _ _ _ above => OperandSourcesAbove.single_move above rfl) (.nil temporary)))
    · simp [LocalPreservation.action, sd]
    · simp [LocalPreservation.action, st]
  have tempP := first3.owner_transfer transfer h.native.valid h.native.callersValid h.native.wellFormed sourceAbove
  have splitWhole : Calling.Prefix callee callers suffix
      ((boxWordActions source destination temporary).take 3 ++ (boxWordActions source destination temporary).drop 3)
      world active final after := by simpa only [List.take_append_drop] using whole
  obtain ⟨wa, aa, actualFirst, remaining⟩ := splitWhole.split
  have same := first3.unique actualFirst
  have am := mp
  have tempValue := valueP
  rw [same.1, same.2] at am tempP
  rw [same.2] at tempValue
  change Calling.Prefix callee callers suffix
    [.call .boxNew [.move (.local temporary)] destination, .storageDead temporary] wa aa final after at remaining
  cases remaining with
  | @cons _ callWorld _ _ callActive _ _ _ cost run cleanup =>
    simp only [Calling.instruction, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨w, a, work⟩, called, last⟩ := run
    cases last
    let callCode := code 3
    have prepared := am.prepare callCode
    have value : (aa.forgetRefs callCode).state temporary = Slot.ofValue (encodeWord result.word) :=
      (LoanEnding.forget_closed _ _ (by rw [tempValue]; exact ofValue_typed (word_typed result.word)) (.adt .word)).trans tempValue
    have one := move_local_source (state := (aa.forgetRefs callCode).state) (slot := temporary)
      (by rw [value]; exact Slot.materialize_ofValue _)
    have arguments : SourceEval.operands (aa.forgetRefs callCode).state [.move (.local temporary)] =
        some ([encodeWord result.word], (aa.forgetRefs callCode).state.set temporary .empty) := by
      simp only [SourceEval.operands, one, bind, Option.bind]
    have typed : SnapshotFieldsTyped [encodeWord result.word] [.adt .word] := .cons (word_typed result.word) .nil
    have output : Types.callOutput .boxNew [.adt .word] = some (.owned (.adt .word)) := by
      simp only [Types.callOutput, ite_true]
    have ready := Derived.call_ready_from_values (callers := callers) prepared.native.valid arguments typed output
    have fresh := Derived.original_helper_call_owner_provenance fuel budget (by dsimp [fuel]; omega) rfl
      prepared.native.valid prepared.native.callersValid prepared.native.wellFormed prepared.native.memoryBound ready
      (OperandSourcesAbove.single_move (tempP.prepare_any callCode) rfl) called
    have checked := Derived.call_spec (Recursive.original_typed_respects budget fuel) prepared.native.valid
      prepared.native.callersValid prepared.native.wellFormed .boxNew [.move (.local temporary)] destination ready called
    have finalFresh := cleanup.owner_transfer (OwnerTransfer.kept rfl (by simp [List.all_cons, LocalPreservation.action, dt]))
      checked.2.2.2.2.1 checked.2.2.2.2.2.1 checked.2.2.2.2.2.2.1 fresh
    refine ⟨minimumFuel, minimumBudget, final, after, machine, countAfter, frameAfter, hole, boxed, temporaryGone,
      destinationRoot, rootsAfter, closedAfter, memoryAfter, finalFresh, ?_, stable⟩
    intro other otherBound notS notD notT otherAbove
    have firstKept := first3.owner_transfer (OwnerTransfer.kept rfl (by
      simp [boxWordActions, LocalPreservation.action, LocalPreservation.expression, LocalPreservation.operand, splitPlace, notS, notD, notT]))
      h.native.valid h.native.callersValid h.native.wellFormed otherAbove
    rw [same.1, same.2] at firstKept
    have countA : aa.count = active.count := actualFirst.shape.2.1
    have keptCall := Derived.call_keeps_owner_provenance (Recursive.original_typed_respects budget fuel)
      prepared.native.valid prepared.native.callersValid prepared.native.wellFormed ready
      (by change other < aa.count; rw [countA]; exact otherBound)
      (by simp [LocalPreservation.action, LocalPreservation.operands, LocalPreservation.operand, splitPlace, notD, notT])
      (firstKept.prepare_any callCode) called
    exact cleanup.owner_transfer (OwnerTransfer.kept rfl (by simp [List.all_cons, LocalPreservation.action, notT]))
      checked.2.2.2.2.1 checked.2.2.2.2.2.1 checked.2.2.2.2.2.2.1 keptCall

end SubtreeProofs.Rust.SourceEval.Evaluator
