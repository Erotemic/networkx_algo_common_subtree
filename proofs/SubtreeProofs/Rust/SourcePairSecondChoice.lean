module

public import SubtreeProofs.Rust.SourcePairFirstChoice

/-! The actual second choice moves the held right witness into 103, selects
against 100 into outer result 99, retires both moved arguments and reads 99. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_second_choice_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (first second : CommonEmbedding)
    (firstValue : active.state 100 = Slot.ofValue (encodeResult first))
    (secondValue : active.state 95 = Slot.ofValue (encodeResult second))
    (firstAbove : LocalOwnersAbove before.memory.length world active 100)
    (secondAbove : LocalOwnersAbove before.memory.length world active 95)
    (heldAbove : ∀ slot ∈ [71, 85], LocalOwnersAbove before.memory.length world active slot)
    (empty99 : active.state 99 = .empty)
    (root99 : ∃ binding, active.roots 99 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 []))
    (count : 104 ≤ active.count) (unbound103 : active.roots 103 = none) :
    ∃ argumentWorld argumentActive callWorld callActive final after,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.state 99 = Slot.ofValue (encodeResult (OrderedSolver.selectResult first second)) ∧
      after.state 95 = .empty ∧ after.state 100 = .empty ∧
      (∀ slot ∈ [100, 103], after.roots slot = none) ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [100, 103] → after.roots slot = active.roots slot) ∧
      LocalOwnersAbove before.memory.length final after 99 ∧
      (∀ slot ∈ [71, 85], LocalOwnersAbove before.memory.length final after slot) ∧
      (∀ slot, slot ∉ [95, 99, 100, 103] → ∀ ty,
        SlotTyped (active.state slot) ty → Borrow.Closed ty → after.state slot = active.state slot) ∧
      (∀ slot ∈ [1, 2], after.state slot = active.state slot) ∧
      (∀ slot binding, slot ≠ 99 → active.roots slot = some binding → ∀ cell,
        world.memory[binding.address]? = some cell → final.memory[binding.address]? = some cell) ∧
      ∀ fuel budget, 0 < fuel →
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 17) ((finishActions.drop 15).take 2) world active argumentWorld argumentActive ∧
        Derived.call (Recursive.original budget fuel) argumentWorld (argumentActive.forgetRefs (finishCode 17)) callers
          .chooseLonger [.move (.local 100), .move (.local 103)] 99 =
            some (callWorld, callActive, choiceCallCost 100 103 99 first second) ∧
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 18)
          [.call .chooseLonger [.move (.local 100), .move (.local 103)] 99] argumentWorld argumentActive callWorld callActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 21) ((finishActions.drop 18).take 3) callWorld callActive final after ∧
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 21) ((finishActions.drop 15).take 6) world active final after := by
  let callee := Helpers.callee 0 0
  obtain ⟨wa, aa, arguments, ma, rootsA, countA, frameA, empty95, value103, memoryA⟩ :=
    original_move_view_complete h callee (finishCode 17) (source := 95) (destination := 103) (by decide) (by decide)
      secondValue (result_typed second) (.adt .embedding) (by omega) unbound103
  have firstA : aa.state 100 = Slot.ofValue (encodeResult first) :=
    (arguments.closed_local_same (index := 100) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [firstValue]; exact ofValue_typed (result_typed first)) (.adt .embedding) rfl (by decide)).trans firstValue
  have firstFresh := arguments.owner_transfer (OwnerTransfer.kept rfl (by decide)) h.native.valid h.native.callersValid h.native.wellFormed firstAbove
  have transfer : OwnerTransfer 95 ((finishActions.drop 15).take 2) 103 :=
    .keep rfl (by decide) (.assign (fun _ _ _ above => OperandSourcesAbove.single_move above rfl) (.nil 103))
  have secondFresh := arguments.owner_transfer transfer h.native.valid h.native.callersValid h.native.wellFormed secondAbove
  have heldA : ∀ slot ∈ [71, 85], LocalOwnersAbove before.memory.length wa aa slot := by
    intro slot member
    exact arguments.owner_transfer (OwnerTransfer.kept rfl (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> decide +kernel)) h.native.valid h.native.callersValid h.native.wellFormed (heldAbove slot member)
  obtain ⟨b99, bound99, raw99⟩ := root99
  have root99A : aa.roots 99 = some b99 := by simpa [rootsA, Roots.set] using bound99
  have empty99A : aa.state 99 = .empty :=
    (arguments.closed_local_same (index := 99) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [empty99]; exact .empty .u32) .u32 rfl (by decide)).trans empty99
  let prepared := aa.forgetRefs (finishCode 17)
  have mp := ma.prepare (finishCode 17)
  obtain ⟨wc, ac, mc, rootsC, countC, frameC, stateC, selectedFresh, heldC, memoryC, stableC⟩ :=
    original_choice_complete mp 100 103 99 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intro index member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            change _ < aa.count <;> rw [countA] <;> omega)
      first second ((ma.prepare_closed_local _ 100 (by decide)).trans firstA)
      ((ma.prepare_closed_local _ 103 (by decide)).trans value103)
      (firstFresh.prepare_any _) (secondFresh.prepare_any _) root99A (memoryA 99 b99 bound99 _ raw99)
      (LoanEnding.forget_empty _ _ empty99A)
  obtain ⟨b100, bound100⟩ := Activation.root_of_materialize (value := encodeResult first) h.native.valid
    (by rw [firstValue]; exact Slot.materialize_ofValue _)
  have root100C : ac.roots 100 = some b100 := by simpa [rootsC, Activation.forgetRefs, rootsA, Roots.set] using bound100
  have root103C : ac.roots 103 = some ⟨world.memory.length, world.memory.length⟩ := by
    simp [rootsC, Activation.forgetRefs, rootsA, Roots.set]
  have plan : RetirementPlan ac.roots ((finishActions.drop 18).take 2) ((ac.roots.set 103 none).set 100 none) :=
    .dead root103C (.dead (by simpa [Roots.set] using root100C) (.nil _))
  have zero : ZeroRetirement ((finishActions.drop 18).take 2) ac.state := by
    intro slot member
    have selected : slot = 103 ∨ slot = 100 := by simpa [finishActions] using member
    rcases selected with rfl | rfl <;> simp [stateC, Partial.Locals.set, Slot.dropWork]
  obtain ⟨final, ar, retired, mr, rootsR, countR, memoryR⟩ := plan.complete_original callee (finishCode 20) mc rfl zero
  let after := ar.forgetRefs (finishCode 20)
  have machine := mr.prepare (finishCode 20)
  have fake : Calling.Prefix callee callers (finishCode 21) [.fakeRead (.local 99)] final ar final after :=
    .cons (Calling.instruction_noncall_run (act := .fakeRead (.local 99)) rfl) (.nil _ _)
  have last3 : Calling.Prefix callee callers (finishCode 21) ((finishActions.drop 18).take 3) wc ac final after :=
    Calling.Prefix.append (suffix := finishCode 21) (rest := [.fakeRead (.local 99)]) retired fake
  have stable : ∀ fuel budget, 0 < fuel →
      Calling.Prefix (Recursive.original budget fuel) callers (finishCode 17) ((finishActions.drop 15).take 2) world active wa aa ∧
      Derived.call (Recursive.original budget fuel) wa prepared callers .chooseLonger [.move (.local 100), .move (.local 103)] 99 =
        some (wc, ac, choiceCallCost 100 103 99 first second) ∧
      Calling.Prefix (Recursive.original budget fuel) callers (finishCode 18) [.call .chooseLonger [.move (.local 100), .move (.local 103)] 99] wa aa wc ac ∧
      Calling.Prefix (Recursive.original budget fuel) callers (finishCode 21) ((finishActions.drop 18).take 3) wc ac final after ∧
      Calling.Prefix (Recursive.original budget fuel) callers (finishCode 21) ((finishActions.drop 15).take 6) world active final after := by
    intro fuel budget positive
    have args := arguments.noncall_callee (Recursive.original budget fuel) (by decide +kernel)
    have called := stableC fuel budget positive
    have callPrefix : Calling.Prefix (Recursive.original budget fuel) callers (finishCode 18)
        [.call .chooseLonger [.move (.local 100), .move (.local 103)] 99] wa aa wc ac :=
      .cons (Calling.instruction_call_run called) (.nil _ _)
    have last := last3.noncall_callee (Recursive.original budget fuel) (by decide +kernel)
    exact ⟨args, called, callPrefix, last, Calling.Prefix.append (suffix := finishCode 21) (rest := (finishActions.drop 17).take 4)
      args (Calling.Prefix.append (suffix := finishCode 21) (rest := (finishActions.drop 18).take 3) callPrefix last)⟩
  have whole := (stable 1 0 (by decide)).2.2.2.2
  have heldFinal : ∀ slot ∈ [71, 85], LocalOwnersAbove before.memory.length final after slot := by
    intro slot member
    have slotBound : slot < prepared.count := by
      change slot < aa.count; rw [countA]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
    have kept := heldC slot slotBound
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega) ((heldA slot member).prepare_any _)
    exact last3.owner_transfer (OwnerTransfer.kept rfl (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> decide +kernel)) mc.native.valid mc.native.callersValid mc.native.wellFormed kept
  have rootsAfter : after.roots = (aa.roots.set 103 none).set 100 none := by change ar.roots = _; rw [rootsR, rootsC]; rfl
  have value99 : ac.state 99 = Slot.ofValue (encodeResult (OrderedSolver.selectResult first second)) := by
    rw [stateC]; simp only [Partial.Locals.set, ite_true]
  have empty95C : ac.state 95 = .empty := by
    rw [stateC]
    simp only [Partial.Locals.set, show (95 : Nat) ≠ 99 by decide, show (95 : Nat) ≠ 103 by decide,
      show (95 : Nat) ≠ 100 by decide, ite_false]
    exact LoanEnding.forget_empty _ _ empty95
  refine ⟨wa, aa, wc, ac, final, after, machine, ?_, ?_, ?_, ?_, countR.trans (countC.trans countA),
    (last3.shape.1).trans (frameC.trans frameA), ?_, ?_, heldFinal, ?_, ?_, ?_, stable⟩
  · exact (last3.closed_local_same (index := 99) mc.native.valid mc.native.callersValid mc.native.wellFormed
      (by rw [value99]; exact ofValue_typed (result_typed _)) (.adt .embedding) rfl (by decide)).trans value99
  · exact (last3.closed_local_same (index := 95) mc.native.valid mc.native.callersValid mc.native.wellFormed
      (by rw [empty95C]; exact .empty .u32) .u32 rfl (by decide)).trans empty95C
  · have missing : after.roots 100 = none := by simp [rootsAfter, Roots.set]
    obtain ⟨_, frame⟩ := machine.native.valid.2
    have localFrame := frame.slots 100
    change (match after.roots 100 with
      | none => after.state 100 = .empty
      | some binding => Anchored final after.frame 100 binding (after.state 100) _) at localFrame
    simpa only [missing] using localFrame
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [rootsAfter, Roots.set]
  · intro slot outside
    have different : slot ≠ 100 ∧ slot ≠ 103 := by simpa using outside
    simp only [rootsAfter, rootsA, Roots.set, different.1, different.2, ite_false]
  · exact last3.owner_transfer (OwnerTransfer.kept rfl (by decide)) mc.native.valid mc.native.callersValid mc.native.wellFormed selectedFresh
  · intro slot outside ty typed closed
    apply whole.closed_local_same_calls typed closed
    have different : slot ≠ 95 ∧ slot ≠ 99 ∧ slot ≠ 100 ∧ slot ≠ 103 := by simpa using outside
    simp [finishActions, LocalPreservation.action, LocalPreservation.expression, LocalPreservation.operands, LocalPreservation.operand,
      splitPlace, different.1, different.2.1, different.2.2.1, different.2.2.2]
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact whole.retained_local_same_calls (by decide +kernel) (by decide +kernel)
  · intro slot binding not99 root cell read
    have not103 : slot ≠ 103 := by intro same; subst slot; rw [unbound103] at root; cases root
    have rootA : aa.roots slot = some binding := by simpa [rootsA, Roots.set, not103] using root
    rw [memoryR]
    exact memoryC slot binding not99 rootA _ (memoryA slot binding root cell read)

end SubtreeProofs.Rust.SourceEval.Evaluator
