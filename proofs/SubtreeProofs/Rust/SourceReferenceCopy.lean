module

public import SubtreeProofs.Rust.SourcePacketAssignment
public import SubtreeProofs.Rust.SourceNativeQueryView

/-! Open a fresh local and copy an existing shared reference through the real
executor. Exact pointer identity is retained for query-tuple loan-origin proofs;
copying a reference does not introduce a fresh loan to either stack root. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem ClosedOutside.enlarge {state : State} {first second : List Nat} (h : ClosedOutside first state)
    (included : first ⊆ second) : ClosedOutside second state :=
  fun index outside => h index (fun member => outside (included member))

theorem ClosedOutside.set_exception {state : State} {exceptions : List Nat} (h : ClosedOutside exceptions state)
    {slot : Nat} (member : slot ∈ exceptions) (part : Slot) : ClosedOutside exceptions (state.set slot part) := by
  intro index outside
  have different : index ≠ slot := by intro same; subst index; exact outside member
  simpa only [Partial.Locals.set, different, ite_false] using h index outside

theorem copy_reference_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active) (callee : Derived.Callees) (suffix : Code)
    {destination query : Nat} {sourceRoot : Binding} {value : Value}
    (queryBinding : active.roots query = some sourceRoot) (initialized : active.state query = .shared value)
    (data : NativeData value) (bound : destination < active.count) (unbound : active.roots destination = none) :
    ∃ final after pointer,
      Calling.Prefix callee callers suffix [.storageLive destination, .assign destination (.use (.copy (.local query)))]
        world active final after ∧ LoanSafeMachine before callers previous external final after ∧
      after.roots = active.roots.set destination (some ⟨world.memory.length, world.memory.length⟩) ∧
      after.count = active.count ∧ after.state destination = .shared value ∧
      final.memory[world.memory.length]? = some (.shared pointer) ∧
      final.memory[sourceRoot.address]? = some (.shared pointer) ∧
      (∀ index, index ≠ destination →
        LoanEnding.endsBeforeObservation index (.step (.storageLive destination)
          (.step (.assign destination (.use (.copy (.local query)))) suffix)) = false →
        LoanEnding.endsBeforeObservation index (.step (.assign destination (.use (.copy (.local query)))) suffix) = false →
        after.state index = active.state index) ∧
      (∀ index binding, active.roots index = some binding → ∀ cell,
        world.memory[binding.address]? = some cell → final.memory[binding.address]? = some cell) ∧
      (∀ exceptions, ClosedOutside exceptions active.state →
        ClosedOutside (destination :: exceptions) after.state) ∧
      (ReferenceQueries active.state → QueryOrigins world active before.memory.length → destination ∉ [1, 2] →
        QueryOrigins final after before.memory.length) := by
  have different : query ≠ destination := by intro same; subst query; rw [unbound] at queryBinding; cases queryBinding
  let next : Code := .step (.assign destination (.use (.copy (.local query)))) suffix
  let code : Code := .step (.storageLive destination) next
  have observed : LoanEnding.endsBeforeObservation query code = false := by
    simp [code, next, LoanEnding.endsBeforeObservation, LoanEnding.avoidsAction, LoanEnding.writes,
      LoanEnding.avoidsExpr, LoanEnding.avoidsOperand, LoanEnding.avoidsPlace, splitPlace, Ne.symm different]
  have nextObserved : LoanEnding.endsBeforeObservation query next = false := by
    simp [next, LoanEnding.endsBeforeObservation, LoanEnding.avoidsAction, LoanEnding.avoidsExpr,
      LoanEnding.avoidsOperand, LoanEnding.avoidsPlace, splitPlace]
  obtain ⟨pointer, sourceMemory⟩ := h.shared_root queryBinding initialized
  let first := active.forgetRefs code
  have firstMachine := h.prepare code
  let openedWorld := world.allocate (.stack first.frame destination world.memory.length) (.node .tuple 0 [])
  let opened : Activation := {first with roots := first.roots.set destination (some ⟨world.memory.length, world.memory.length⟩), state := first.state.set destination .empty}
  obtain ⟨openedRun, openedMachine⟩ := firstMachine.storageLive bound unbound
  change LoanSafeMachine before callers previous external openedWorld opened at openedMachine
  let prepared := opened.forgetRefs next
  have preparedMachine := openedMachine.prepare next
  have sourceBinding : prepared.roots query = some sourceRoot := by
    simpa only [prepared, opened, first, Activation.forgetRefs, Roots.set, different, ite_false] using queryBinding
  have input : prepared.state query = .shared value := by
    rw [Activation.forgetRefs_observed opened next query nextObserved]
    simp only [opened, Partial.Locals.set, different, ite_false]
    rw [Activation.forgetRefs_observed active code query observed]
    exact initialized
  have sourceRaw : openedWorld.memory[sourceRoot.address]? = some (.shared pointer) :=
    (world.allocate_keeps h.wellFormed _ _ []).memory _ _ sourceMemory
  have destinationBinding : prepared.roots destination = some ⟨world.memory.length, world.memory.length⟩ := by
    simp [prepared, opened, Roots.set, Activation.forgetRefs]
  have empty : prepared.state destination = .empty := by
    apply LoanEnding.forget_empty
    simp only [opened, Partial.Locals.set, ite_true]
  obtain ⟨assigned, finalMachine⟩ := preparedMachine.assign_packet_empty destinationBinding (world.allocate_spec _ _).2.1
    (fun current suspended _ _ => copy_shared_packet sourceBinding sourceRaw input _)
    empty preparedMachine.safe (by simpa only [Slot.ofValue] using LoanSafe.shared data)
  let final := openedWorld.write world.memory.length (.shared pointer)
  let after : Activation := {prepared with state := prepared.state.set destination (.shared value)}
  simp only [Slot.ofValue] at assigned finalMachine
  change LoanSafeMachine before callers previous external final after at finalMachine
  refine ⟨final, after, pointer,
    .cons (Calling.instruction_noncall_run (act := .storageLive destination) openedRun)
      (.cons (Calling.instruction_noncall_run (act := .assign destination (.use (.copy (.local query)))) assigned) (.nil _ _)),
    finalMachine, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [after, Partial.Locals.set, ite_true]
  · exact (openedWorld.write_spec (by simp only [openedWorld, World.allocate, List.length_append, List.length_singleton]; omega) _).1
  · exact Evaluator.Activation.write_other_root preparedMachine.valid destinationBinding sourceBinding (Ne.symm different) sourceRaw _
  · intro index other firstObserved secondObserved
    simp only [after, Partial.Locals.set, other, ite_false]
    rw [Activation.forgetRefs_observed opened next index secondObserved]
    simp only [opened, Partial.Locals.set, other, ite_false]
    rw [Activation.forgetRefs_observed active code index firstObserved]
  · intro index binding root raw read
    have other : index ≠ destination := by intro same; subst index; rw [unbound] at root; cases root
    have bindingNow : prepared.roots index = some binding := by
      simpa only [prepared, opened, first, Roots.set, Activation.forgetRefs, other, ite_false] using root
    exact Evaluator.Activation.write_other_root preparedMachine.valid destinationBinding bindingNow (Ne.symm other)
      ((world.allocate_keeps h.wellFormed _ _ []).memory _ _ read) _
  · intro exceptions closed
    have enlarged := closed.enlarge (second := destination :: exceptions) (fun _ member => List.mem_cons_of_mem _ member)
    exact ((enlarged.forget code _).clear destination |>.forget next _).set_exception (by simp) _
  · intro refs queries other
    have qOpened := (queries.prepare code).allocate firstMachine.wellFormed destination other
    change QueryOrigins openedWorld opened before.memory.length at qOpened
    have openedRefs : ReferenceQueries opened.state := (refs.prepare code _).set_other destination other .empty
    have finalOrigins := (qOpened.prepare next).write_other preparedMachine.valid (openedRefs.prepare next _)
      destinationBinding other (preparedMachine.fresh destination _ destinationBinding) (.shared pointer)
    exact finalOrigins.set_other destination other (.shared value)

end SubtreeProofs.Rust.SourceEval.Addressed
