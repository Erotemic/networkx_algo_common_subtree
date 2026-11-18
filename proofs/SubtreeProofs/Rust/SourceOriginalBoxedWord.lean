module

public import SubtreeProofs.Rust.SourceOriginalBoxNew
public import SubtreeProofs.Rust.SourceOriginalProjectView
public import SubtreeProofs.Rust.SourceOriginalOpenLocal
public import SubtreeProofs.Rust.SourceOriginalRetirement
public import SubtreeProofs.Rust.SourcePrefixFrame

/-! Move a native embedding's word through a temporary into an actual new Box,
then retire the moved temporary. This common five-instruction sequence retains
the embedding's scalar field and all untouched closed locals and root bytes. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def resultWordHole (edges : Aeneas.Std.U32) : Slot := .node .embedding 0 [.empty, .number edges.val]

theorem resultWordHole_typed (edges : Aeneas.Std.U32) : SlotTyped (resultWordHole edges) (.adt .embedding) :=
  .node .embedding (.cons (.empty (.adt .word)) (.cons (.number edges.hmax) .nil))

theorem result_word_take (result : CommonEmbedding) :
    (Slot.ofValue (encodeResult result)).take [.field none 0] = some (encodeWord result.word, resultWordHole result.edges) := by
  simp [encodeResult, Slot.ofValue, ofFields, Slot.take, Slot.materialize_ofValue, resultWordHole]

def boxWordActions (source destination temporary : Nat) : List Action :=
  [.storageLive destination, .storageLive temporary, .assign temporary (.use (.move (.field (.local source) none 0))),
   .call .boxNew [.move (.local temporary)] destination, .storageDead temporary]

def boxWordCode (source destination temporary : Nat) (suffix : Code) (index : Nat) : Code :=
  ((boxWordActions source destination temporary).drop index).foldr Control.Tree.step suffix

theorem original_boxed_word_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active)
    (source destination temporary : Nat) (sd : source ≠ destination) (st : source ≠ temporary) (dt : destination ≠ temporary)
    (sourceOutside : source ∉ exceptions) (outside : destination ∉ exceptions) (temporaryOutside : temporary ∉ exceptions)
    (bounded : ∀ index ∈ exceptions, index < active.count)
    (destinationBound : destination < active.count) (temporaryBound : temporary < active.count)
    (destinationUnbound : active.roots destination = none) (temporaryUnbound : active.roots temporary = none)
    (result : CommonEmbedding) (initialized : active.state source = Slot.ofValue (encodeResult result)) (suffix : Code) :
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
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers suffix (boxWordActions source destination temporary) world active final after := by
  let code := boxWordCode source destination temporary suffix
  let callee := Helpers.callee 0 0
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
  let rootD : Binding := ⟨world.memory.length, world.memory.length⟩
  have rootD_ad : ad.roots destination = some rootD := by simp [rootsD, rootD, Roots.set]
  have rootD_ap : ap.roots destination = some rootD := by simpa [rootsP, Roots.set, dt] using rootD_ad
  have emptyP : ap.state destination = .empty :=
    (projected.closed_local_same (index := destination) md.native.valid md.native.callersValid md.native.wellFormed
      (by rw [emptyD]; exact .empty .u32) .u32 rfl
      (by simp [LocalPreservation.action, LocalPreservation.expression, LocalPreservation.operand, splitPlace, dt, Ne.symm sd])).trans emptyD
  let observed := ap.forgetRefs (code 3)
  have mc := mp.prepare (code 3)
  obtain ⟨fuel, budget, wc, ac, machineC, rootsC, countC, frameC, stateC, memoryC, stable⟩ :=
    original_box_new_complete mc temporary destination dt temporaryOutside outside
      (by intro index member; change index < ap.count; rw [countP, countD]; exact bounded index member)
      ((mp.prepare_closed_local _ temporary temporaryOutside).trans valueP) (word_typed result.word) (.adt .word)
      rootD_ap (memoryP destination rootD rootD_ad _ rawD) (LoanEnding.forget_empty _ _ emptyP)
  let rootT : Binding := ⟨wd.memory.length, wd.memory.length⟩
  have boundT : ap.roots temporary = some rootT := by simp [rootsP, Roots.set, rootT]
  have plan : RetirementPlan ac.roots [.storageDead temporary] (ac.roots.set temporary none) :=
    .dead (by rw [rootsC]; exact boundT) (.nil _)
  have zero : ZeroRetirement [.storageDead temporary] ac.state := by
    intro slot member
    have same : slot = temporary := by simpa using member
    subst slot; simp [stateC, Partial.Locals.set, Ne.symm dt, Slot.dropWork]
  obtain ⟨final, after, retired, machine, rootsAfter, countAfter, memoryAfter⟩ := plan.complete_original callee suffix machineC rfl zero
  have closedSame : ∀ slot, slot ≠ destination → slot ≠ temporary → ∀ ty,
      SlotTyped (ap.state slot) ty → Borrow.Closed ty → after.state slot = ap.state slot := by
    intro slot notD notT ty typed closed
    have atCall : ac.state slot = ap.state slot := by
      rw [stateC]
      simp only [Partial.Locals.set, notD, notT, ite_false]
      exact LoanEnding.forget_closed _ _ typed closed
    exact (retired.closed_local_same (index := slot) machineC.native.valid machineC.native.callersValid machineC.native.wellFormed
      (by rw [atCall]; exact typed) closed rfl (by simp [LocalPreservation.action, notT])).trans atCall
  refine ⟨fuel, budget, final, after, machine, countAfter.trans (countC.trans (countP.trans countD)),
    (retired.frame_count machineC.native.valid machineC.native.callersValid machineC.native.wellFormed rfl).1.trans (frameC.trans (frameP.trans frameD)),
    ?_, ?_, ?_, ⟨rootD, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact (closedSame source sd st (.adt .embedding) (by rw [holeP]; exact resultWordHole_typed result.edges) (.adt .embedding)).trans holeP
  · have value : ac.state destination = Slot.ofValue (.boxed (encodeWord result.word)) := by simp only [stateC, Partial.Locals.set, ite_true]
    exact (retired.closed_local_same (index := destination) machineC.native.valid machineC.native.callersValid machineC.native.wellFormed
      (by rw [value]; exact ofValue_typed (.owned (word_typed result.word))) (.owned (.adt .word)) rfl
      (by simp [LocalPreservation.action, dt])).trans value
  · simp [rootsAfter, Roots.set]
  · simpa [rootsAfter, rootsC, Activation.forgetRefs, Roots.set, dt] using rootD_ap
  · intro slot notD notT
    simp only [rootsAfter, rootsC, rootsP, rootsD, Activation.forgetRefs, Roots.set, notD, notT, ite_false]
  · intro slot notS notD notT ty typed closed
    have initialSame := first3.closed_local_same (index := slot) h.native.valid h.native.callersValid h.native.wellFormed typed closed rfl
      (by simp [boxWordActions, LocalPreservation.action, LocalPreservation.expression, LocalPreservation.operand, splitPlace, notS, notD, notT])
    exact (closedSame slot notD notT ty (by rw [initialSame]; exact typed) closed).trans initialSame
  · intro index binding root raw memoryRead
    have notD : index ≠ destination := by intro same; subst index; rw [destinationUnbound] at root; cases root
    have notT : index ≠ temporary := by intro same; subst index; rw [temporaryUnbound] at root; cases root
    have root_ad : ad.roots index = some binding := by simpa only [rootsD, Roots.set, notD, ite_false] using root
    have root_ap : ap.roots index = some binding := by simpa only [rootsP, Roots.set, notT, ite_false] using root_ad
    rw [memoryAfter]
    exact memoryC index binding notD root_ap _ (memoryP index binding root_ad _ (memoryD index binding root _ memoryRead))
  · intro largerFuel largerBudget fuelBound budgetBound
    have callRun : Calling.Prefix (Recursive.original largerBudget largerFuel) callers (code 4)
        [.call .boxNew [.move (.local temporary)] destination] wp ap wc ac :=
      .cons (Calling.instruction_call_run (stable largerFuel largerBudget fuelBound budgetBound)) (.nil _ _)
    exact Calling.Prefix.append (suffix := suffix) (rest := [.call .boxNew [.move (.local temporary)] destination, .storageDead temporary])
      (first3.noncall_callee _ rfl) (Calling.Prefix.append (suffix := suffix) (rest := [.storageDead temporary]) callRun
        (retired.noncall_callee _ rfl))

end SubtreeProofs.Rust.SourceEval.Evaluator
