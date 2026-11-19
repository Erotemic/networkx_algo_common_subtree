module

public import SubtreeProofs.Rust.SourceMaximumCleanup

/-! Construct the complete public body from native readable queries. Actual
entry, all 17 instructions, recursive evaluation, owned table teardown and
return are composed without a successful parent execution premise. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Maximum

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem entry_body_complete {world : World} {callers : List Activation} {previous : Resources}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (left right : BalancedWord) (leftCell rightCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord left)))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord right)))
    {external : List Nat} (frame : OwnerFrame world (callerOwners world callers ++ external))
    (covered : BoxCoverage world (callerOwners world callers ++ external)) :
    ∃ entered active fuel budget middle after cell result output work,
      enter world world.memory.length CallingCertificate.originalMaximum.source.localCount
        (inputPackets leftCell rightCell left right) = some (entered, active) ∧
      LoanSafeMachine world callers previous external entered active ∧
      active.state = initialState [.reference (encodeWord left), .reference (encodeWord right)] ∧
      Calling.exec (Recursive.original budget fuel) callers body entered active =
        some (.returned middle after (cell, encodeOption result), work) ∧
      memoized_common_embedding left right .Empty = .ok (result, output) ∧
      maximum_common_embedding left right = .ok result ∧
      (∀ slot, after.state slot = .empty) ∧ after.RootsSeparate callers ∧
      (∀ slot binding, after.roots slot = some binding → world.memory.length ≤ binding.address) ∧
      Preserves world middle previous.reads := by
  obtain ⟨entered, active, entry, initial, state, count, unbound⟩ :=
    native_entry_machine hw hc view left right leftCell rightCell leftRead rightRead frame covered
  have first : active.state 1 = .shared (encodeWord left) := by
    rw [state]; simp [initialState, Partial.Locals.lift, initialEnv, Slot.ofValue]
  have second : active.state 2 = .shared (encodeWord right) := by
    rw [state]; simp [initialState, Partial.Locals.lift, initialEnv, Slot.ofValue]
  obtain ⟨root1, bound1⟩ := Activation.root_of_materialize initial.native.valid
    (slot := 1) (by rw [first]; exact (show (Slot.shared (encodeWord left)).materialize = some (.reference (encodeWord left)) by simp only [Slot.materialize]))
  obtain ⟨root2, bound2⟩ := Activation.root_of_materialize initial.native.valid
    (slot := 2) (by rw [second]; exact (show (Slot.shared (encodeWord right)).materialize = some (.reference (encodeWord right)) by simp only [Slot.materialize]))
  obtain ⟨preparedWorld, prepared, root0, root3, preparation, preparedMachine, preparedCount, _,
    bound0, bound3, raw0, raw3, empty0, empty3, first4, second5, table6, otherRoots⟩ :=
    preparation_complete initial (Helpers.callee 0 0) (by omega) left right first second
      (by intro slot member; apply unbound; simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; omega)
  obtain ⟨root4, bound4⟩ := Activation.root_of_materialize preparedMachine.native.valid
    (slot := 4) (by rw [first4]; exact (show (Slot.shared (encodeWord left)).materialize = some (.reference (encodeWord left)) by simp only [Slot.materialize]))
  obtain ⟨root5, bound5⟩ := Activation.root_of_materialize preparedMachine.native.valid
    (slot := 5) (by rw [second5]; exact (show (Slot.shared (encodeWord right)).materialize = some (.reference (encodeWord right)) by simp only [Slot.materialize]))
  obtain ⟨root6, bound6⟩ := Activation.root_of_materialize preparedMachine.native.valid
    (slot := 6) (by rw [table6]; exact Slot.materialize_ofValue _)
  obtain ⟨fuel, budget, calledWorld, called, result, output, callCost, callMachine, callRoots, callCount, _,
    callOutput, emptyArgs, native, freshOutput, callMemory, unchanged, stable⟩ :=
    evaluate_call_complete preparedMachine (by omega) left right first4 second5 table6 bound3 raw3 empty3
  have calledCount : called.count = 7 := callCount.trans (preparedCount.trans count)
  have called0 : called.roots 0 = some root0 := by rw [callRoots]; exact bound0
  have called1 : called.roots 1 = some root1 := by rw [callRoots, otherRoots 1 (by decide)]; exact bound1
  have called2 : called.roots 2 = some root2 := by rw [callRoots, otherRoots 2 (by decide)]; exact bound2
  have called3 : called.roots 3 = some root3 := by rw [callRoots]; exact bound3
  have called4 : called.roots 4 = some root4 := by rw [callRoots]; exact bound4
  have called5 : called.roots 5 = some root5 := by rw [callRoots]; exact bound5
  have called6 : called.roots 6 = some root6 := by rw [callRoots]; exact bound6
  have calledEmpty0 : called.state 0 = .empty :=
    (unchanged 0 (by decide) (by rw [empty0]; simp)).trans empty0
  have calledRaw0 := callMemory 0 root0 (by decide) bound0 _ raw0
  obtain ⟨middle, after, cell, cleanupCost, cleanup, empty, separate, fresh, kept⟩ :=
    cleanup_complete callMachine (Recursive.original budget fuel) calledCount callOutput freshOutput
      called0 called1 called2 called3 called4 called5 called6 calledRaw0 calledEmpty0 emptyArgs
  have tail : Calling.exec (Recursive.original budget fuel) callers callCode preparedWorld prepared =
      some (.returned middle after (cell, encodeOption result), callCost.plus cleanupCost) := by
    rw [callCode, Calling.exec_step]
    change (do
      let ((middle, current), first) ← Calling.instruction (Recursive.original budget fuel) callers
        (preparedWorld, prepared.forgetRefs callCode) evaluateCall
      let (flow, last) ← Calling.exec (Recursive.original budget fuel) callers (afterCall.foldr Control.Tree.step .ret) middle current
      some (flow, first.plus last)) = _
    simp only [stable fuel budget (by rfl) (by rfl), cleanup, bind, Option.bind]
  obtain ⟨work, bodyRun⟩ := (preparation.noncall_callee (Recursive.original budget fuel) (by decide +kernel)).exec tail
  rw [← body_preparation] at bodyRun
  have publicNative : maximum_common_embedding left right = .ok result := by
    simp only [maximum_common_embedding, native, Aeneas.Std.bind_ok]
    rfl
  exact ⟨entered, active, fuel, budget, middle, after, cell, result, output, work, entry,
    initial.native, state, bodyRun, native, publicNative, empty, separate, fresh, kept⟩

end SubtreeProofs.Rust.SourceEval.Maximum
