module

public import SubtreeProofs.Rust.SourceOriginalMoveInto
public import SubtreeProofs.Rust.SourcePairTailProgram
public import SubtreeProofs.Rust.SourceOriginalRetirement
public import SubtreeProofs.Rust.SourcePrefixIdentity

/-! Move a successful native optional embedding through fresh scratch storage
into an existing empty payload local. The scratch owner transfer, moved-out
drop and stack retirement follow the actual six-instruction source pattern. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def optionalPayloadActions (source temporary destination : Nat) : List Action :=
  [.storageLive temporary, .assign temporary (.use (.move (.field (.local source) (some 1) 0))),
   .assign destination (.use (.move (.local temporary))), .drop temporary, .storageDead temporary, .fakeRead (.local destination)]

theorem original_optional_payload_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active) (callee : Derived.Callees) (suffix : Code)
    (source temporary destination : Nat) (sourceTemp : source ≠ temporary) (sourceDestination : source ≠ destination) (tempDestination : temporary ≠ destination)
    (outside : ∀ slot ∈ [source, temporary, destination], slot ∉ exceptions)
    (witness : CommonEmbedding) (value : active.state source = Slot.ofValue (encodeOption (some witness)))
    (empty : active.state destination = .empty) {binding : Binding} (root : active.roots destination = some binding)
    (raw : world.memory[binding.address]? = some (.node .tuple 0 []))
    (bound : temporary < active.count) (unbound : active.roots temporary = none) :
    ∃ final after,
      Calling.Prefix callee callers suffix (optionalPayloadActions source temporary destination) world active final after ∧
      OriginalLoanMachine before callers previous external exceptions final after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      after.state source = headPayloadHole ∧ after.state destination = Slot.ofValue (encodeResult witness) ∧
      after.roots temporary = none ∧
      (∀ index binding, index ≠ destination → active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  let after2 : Code := ((optionalPayloadActions source temporary destination).drop 2).foldr Control.Tree.step suffix
  obtain ⟨wp, ap, project, mp, rootsP, countP, frameP, holeP, valueP, memoryP⟩ :=
    original_project_view_complete h callee after2 (source := source) (destination := temporary)
      (place := .field (.local source) (some 1) 0) (outside _ (by simp)) (outside _ (by simp)) sourceTemp rfl trivial
      (by rw [value]; exact head_payload_take witness) headPayloadHole_typed (.adt .optional)
      (result_typed witness) (.adt .embedding) bound unbound
  have rootP : ap.roots destination = some binding := by simpa [rootsP, Roots.set, Ne.symm tempDestination] using root
  have emptyP : ap.state destination = .empty :=
    (project.closed_local_same_calls (index := destination) (by rw [empty]; exact .empty .u32) .u32
      (by simp [LocalPreservation.action, LocalPreservation.expression, LocalPreservation.operand, splitPlace,
            Ne.symm tempDestination, Ne.symm sourceDestination])).trans empty
  let after3 : Code := ((optionalPayloadActions source temporary destination).drop 3).foldr Control.Tree.step suffix
  obtain ⟨wa, aa, assigned, ma, rootsA, countA, frameA, moved, valueA, memoryA⟩ :=
    original_move_into_complete mp callee after3 (source := temporary) (destination := destination)
      (outside _ (by simp)) (outside _ (by simp)) tempDestination valueP (result_typed witness) (.adt .embedding)
      rootP (memoryP destination binding root _ raw) emptyP
  have boundTemp : aa.roots temporary = some ⟨world.memory.length, world.memory.length⟩ := by simp [rootsA, rootsP, Roots.set]
  have plan : RetirementPlan aa.roots [.drop temporary, .storageDead temporary] (aa.roots.set temporary none) :=
    .drop boundTemp (.dead boundTemp (.nil _))
  have zero : ZeroRetirement [.drop temporary, .storageDead temporary] aa.state := by
    intro slot member
    have same : slot = temporary := by simpa using member
    subst slot; rw [moved]; simp only [Slot.dropWork]
  obtain ⟨final, ar, retirement, mr, rootsR, countR, memoryR⟩ := plan.complete_original callee (.step (.fakeRead (.local destination)) suffix) ma rfl zero
  let after := ar.forgetRefs (.step (.fakeRead (.local destination)) suffix)
  have machine := mr.prepare (.step (.fakeRead (.local destination)) suffix)
  have last3 : Calling.Prefix callee callers suffix ((optionalPayloadActions source temporary destination).drop 3) wa aa final after :=
    Calling.Prefix.append (suffix := suffix) (rest := [.fakeRead (.local destination)]) retirement
      (.cons (Calling.instruction_noncall_run (act := .fakeRead (.local destination)) rfl) (.nil _ _))
  have last4 : Calling.Prefix callee callers suffix ((optionalPayloadActions source temporary destination).drop 2) wp ap final after :=
    Calling.Prefix.append (suffix := suffix) (rest := (optionalPayloadActions source temporary destination).drop 3) assigned last3
  have whole : Calling.Prefix callee callers suffix (optionalPayloadActions source temporary destination) world active final after :=
    Calling.Prefix.append (suffix := suffix) (rest := (optionalPayloadActions source temporary destination).drop 2) project last4
  refine ⟨final, after, whole, machine, ?_, whole.shape.2.1, whole.shape.1, ?_, ?_, ?_, ?_⟩
  · change ar.roots = active.roots
    rw [rootsR, rootsA, rootsP]
    funext slot
    by_cases same : slot = temporary
    · subst slot; simpa [Roots.set] using unbound.symm
    · simp [Roots.set, same]
  · exact (last4.closed_local_same_calls (index := source) (by rw [holeP]; exact headPayloadHole_typed) (.adt .optional)
      (by simp [optionalPayloadActions, LocalPreservation.action, LocalPreservation.expression, LocalPreservation.operand,
            splitPlace, sourceTemp, sourceDestination])).trans holeP
  · exact (last3.closed_local_same_calls (index := destination) (by rw [valueA]; exact ofValue_typed (result_typed witness)) (.adt .embedding)
      (by simp [optionalPayloadActions, LocalPreservation.action, Ne.symm tempDestination])).trans valueA
  · change ar.roots temporary = none
    simp [rootsR, Roots.set]
  · intro index other different rootBefore rawCell memoryRead
    have notTemp : index ≠ temporary := by intro same; subst index; rw [unbound] at rootBefore; cases rootBefore
    have rootProject : ap.roots index = some other := by simpa only [rootsP, Roots.set, notTemp, ite_false] using rootBefore
    rw [memoryR]
    exact memoryA index other different rootProject rawCell (memoryP index other rootBefore rawCell memoryRead)

end SubtreeProofs.Rust.SourceEval.Evaluator
