module

public import SubtreeProofs.Rust.SourceOriginalChoice
public import SubtreeProofs.Rust.SourceOriginalMoveView
public import SubtreeProofs.Rust.SourceOriginalOpenLocal
public import SubtreeProofs.Rust.SourceOriginalRetirement
public import SubtreeProofs.Rust.SourcePairFinishProvenance

/-! Construct the actual first-choice region: outer/result storage, two moved
arguments, the real recursive choice and physical argument retirement. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_first_choice_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (first second : CommonEmbedding)
    (firstValue : active.state 64 = Slot.ofValue (encodeResult first))
    (secondValue : active.state 81 = Slot.ofValue (encodeResult second))
    (firstAbove : LocalOwnersAbove before.memory.length world active 64)
    (secondAbove : LocalOwnersAbove before.memory.length world active 81)
    (heldAbove : ∀ slot ∈ [71, 85, 95], LocalOwnersAbove before.memory.length world active slot)
    (count : 103 ≤ active.count) (unbound : ∀ slot ∈ [99, 100, 101, 102], active.roots slot = none) :
    ∃ argumentWorld argumentActive callWorld callActive final after,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.state 100 = Slot.ofValue (encodeResult (OrderedSolver.selectResult first second)) ∧
      after.state 64 = .empty ∧ after.state 81 = .empty ∧ after.state 99 = .empty ∧
      (∃ binding, after.roots 99 = some binding ∧ final.memory[binding.address]? = some (.node .tuple 0 [])) ∧
      (∀ slot ∈ [101, 102], after.roots slot = none) ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [99, 100, 101, 102] → after.roots slot = active.roots slot) ∧
      LocalOwnersAbove before.memory.length final after 100 ∧
      (∀ slot ∈ [71, 85, 95], LocalOwnersAbove before.memory.length final after slot) ∧
      (∀ slot, slot ∉ [64, 81, 99, 100, 101, 102] → ∀ ty,
        SlotTyped (active.state slot) ty → Borrow.Closed ty → after.state slot = active.state slot) ∧
      (∀ slot ∈ [1, 2], after.state slot = active.state slot) ∧
      (∀ slot binding, active.roots slot = some binding → ∀ cell,
        world.memory[binding.address]? = some cell → final.memory[binding.address]? = some cell) ∧
      ∀ fuel budget, 0 < fuel →
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 12) ((finishActions.drop 6).take 6) world active argumentWorld argumentActive ∧
        Derived.call (Recursive.original budget fuel) argumentWorld (argumentActive.forgetRefs (finishCode 12)) callers
          .chooseLonger [.move (.local 101), .move (.local 102)] 100 =
            some (callWorld, callActive, choiceCallCost 101 102 100 first second) ∧
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 13)
          [.call .chooseLonger [.move (.local 101), .move (.local 102)] 100] argumentWorld argumentActive callWorld callActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 15) ((finishActions.drop 13).take 2) callWorld callActive final after ∧
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 15) ((finishActions.drop 6).take 9) world active final after := by
  let callee := Helpers.callee 0 0
  obtain ⟨w99, a99, run99, m99, roots99, count99, frame99, empty99, raw99, memory99⟩ :=
    original_open_local_complete h callee (finishCode 7) (slot := 99) (by decide) (by omega) (unbound 99 (by simp))
  obtain ⟨wd, ad, run100, md, roots100, count100, frame100, empty100, raw100, memory100⟩ :=
    original_open_local_complete m99 callee (finishCode 8) (slot := 100) (by decide) (by rw [count99]; omega)
      (by simpa [roots99, Roots.set] using unbound 100 (by simp))
  have first2 : Calling.Prefix callee callers (finishCode 8) ((finishActions.drop 6).take 2) world active wd ad :=
    Calling.Prefix.append (suffix := finishCode 8) (rest := [.storageLive 100]) run99 run100
  have firstD : ad.state 64 = Slot.ofValue (encodeResult first) :=
    (first2.closed_local_same (index := 64) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [firstValue]; exact ofValue_typed (result_typed first)) (.adt .embedding) rfl (by decide +kernel)).trans firstValue
  obtain ⟨wl, al, runLeft, ml, rootsL, countL, frameL, empty64, value101, memoryL⟩ :=
    original_move_view_complete md callee (finishCode 10) (source := 64) (destination := 101) (by decide) (by decide)
      firstD (result_typed first) (.adt .embedding) (by rw [count100, count99]; omega)
      (by simpa [roots100, roots99, Roots.set] using unbound 101 (by simp))
  have secondD : ad.state 81 = Slot.ofValue (encodeResult second) :=
    (first2.closed_local_same (index := 81) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [secondValue]; exact ofValue_typed (result_typed second)) (.adt .embedding) rfl (by decide +kernel)).trans secondValue
  have secondL : al.state 81 = Slot.ofValue (encodeResult second) :=
    (runLeft.closed_local_same (index := 81) md.native.valid md.native.callersValid md.native.wellFormed
      (by rw [secondD]; exact ofValue_typed (result_typed second)) (.adt .embedding) rfl (by decide +kernel)).trans secondD
  obtain ⟨wa, aa, runRight, ma, rootsA, countA, frameA, empty81, value102, memoryA⟩ :=
    original_move_view_complete ml callee (finishCode 12) (source := 81) (destination := 102) (by decide) (by decide)
      secondL (result_typed second) (.adt .embedding) (by rw [countL, count100, count99]; omega)
      (by simpa [rootsL, roots100, roots99, Roots.set] using unbound 102 (by simp))
  have last4 : Calling.Prefix callee callers (finishCode 12) ((finishActions.drop 8).take 4) wd ad wa aa :=
    Calling.Prefix.append (suffix := finishCode 12) (rest := [.storageLive 102, .assign 102 (.use (.move (.local 81)))]) runLeft runRight
  have arguments : Calling.Prefix callee callers (finishCode 12) ((finishActions.drop 6).take 6) world active wa aa :=
    Calling.Prefix.append (suffix := finishCode 12) (rest := (finishActions.drop 8).take 4) first2 last4
  have leftPlan : OwnerTransfer 64 ((finishActions.drop 6).take 6) 101 :=
    .keep rfl (by decide) (.keep rfl (by decide) (.keep rfl (by decide)
      (.assign (fun _ _ _ above => OperandSourcesAbove.single_move above rfl)
        (.keep rfl (by decide) (.keep rfl (by decide) (.nil 101))))))
  have rightPlan : OwnerTransfer 81 ((finishActions.drop 6).take 6) 102 :=
    .keep rfl (by decide) (.keep rfl (by decide) (.keep rfl (by decide) (.keep rfl (by decide)
      (.keep rfl (by decide) (.assign (fun _ _ _ above => OperandSourcesAbove.single_move above rfl) (.nil 102))))))
  have leftFresh := arguments.owner_transfer leftPlan h.native.valid h.native.callersValid h.native.wellFormed firstAbove
  have rightFresh := arguments.owner_transfer rightPlan h.native.valid h.native.callersValid h.native.wellFormed secondAbove
  have heldA : ∀ slot ∈ [71, 85, 95], LocalOwnersAbove before.memory.length wa aa slot := by
    intro slot member
    exact arguments.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide +kernel)) h.native.valid h.native.callersValid h.native.wellFormed (heldAbove slot member)
  let b99 : Binding := ⟨world.memory.length, world.memory.length⟩
  let b100 : Binding := ⟨w99.memory.length, w99.memory.length⟩
  have root99D : ad.roots 99 = some b99 := by simp [roots100, roots99, Roots.set, b99]
  have root99L : al.roots 99 = some b99 := by simpa [rootsL, Roots.set] using root99D
  have root99A : aa.roots 99 = some b99 := by simpa [rootsA, Roots.set] using root99L
  have root100D : ad.roots 100 = some b100 := by simp [roots100, Roots.set, b100]
  have root100L : al.roots 100 = some b100 := by simpa [rootsL, Roots.set] using root100D
  have root100A : aa.roots 100 = some b100 := by simpa [rootsA, Roots.set] using root100L
  have raw99A : wa.memory[b99.address]? = some (.node .tuple 0 []) :=
    memoryA 99 b99 root99L _ (memoryL 99 b99 root99D _ (memory100 99 b99 (by simp [roots99, Roots.set, b99]) _ raw99))
  have raw100A : wa.memory[b100.address]? = some (.node .tuple 0 []) :=
    memoryA 100 b100 root100L _ (memoryL 100 b100 root100D _ raw100)
  have empty100A : aa.state 100 = .empty :=
    (last4.closed_local_same (index := 100) md.native.valid md.native.callersValid md.native.wellFormed
      (by rw [empty100]; exact .empty .u32) .u32 rfl (by decide +kernel)).trans empty100
  have firstA : aa.state 101 = Slot.ofValue (encodeResult first) :=
    (runRight.closed_local_same (index := 101) ml.native.valid ml.native.callersValid ml.native.wellFormed
      (by rw [value101]; exact ofValue_typed (result_typed first)) (.adt .embedding) rfl (by decide +kernel)).trans value101
  let prepared := aa.forgetRefs (finishCode 12)
  have mp := ma.prepare (finishCode 12)
  obtain ⟨wc, ac, mc, rootsC, countC, frameC, stateC, selectedFresh, heldC, memoryC, stableC⟩ :=
    original_choice_complete mp 101 102 100 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intro index member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            change _ < aa.count <;> rw [countA, countL, count100, count99] <;> omega)
      first second ((ma.prepare_closed_local _ 101 (by decide)).trans firstA)
      ((ma.prepare_closed_local _ 102 (by decide)).trans value102)
      (leftFresh.prepare_any _) (rightFresh.prepare_any _) root100A raw100A (LoanEnding.forget_empty _ _ empty100A)
  have bound101 : ac.roots 101 = some ⟨wd.memory.length, wd.memory.length⟩ := by
    simp [rootsC, Activation.forgetRefs, rootsA, rootsL, Roots.set]
  have bound102 : ac.roots 102 = some ⟨wl.memory.length, wl.memory.length⟩ := by
    simp [rootsC, Activation.forgetRefs, rootsA, Roots.set]
  have plan : RetirementPlan ac.roots ((finishActions.drop 13).take 2) ((ac.roots.set 102 none).set 101 none) :=
    .dead bound102 (.dead (by simpa [Roots.set] using bound101) (.nil _))
  have zero : ZeroRetirement ((finishActions.drop 13).take 2) ac.state := by
    intro slot member
    have cases : slot = 102 ∨ slot = 101 := by simpa [finishActions] using member
    rcases cases with rfl | rfl <;> simp [stateC, Partial.Locals.set, Slot.dropWork]
  obtain ⟨final, after, cleanup, machine, rootsAfter, countAfter, memoryAfter⟩ := plan.complete_original callee (finishCode 15) mc rfl zero
  have stable : ∀ fuel budget, 0 < fuel →
      Calling.Prefix (Recursive.original budget fuel) callers (finishCode 12) ((finishActions.drop 6).take 6) world active wa aa ∧
      Derived.call (Recursive.original budget fuel) wa prepared callers .chooseLonger [.move (.local 101), .move (.local 102)] 100 =
        some (wc, ac, choiceCallCost 101 102 100 first second) ∧
      Calling.Prefix (Recursive.original budget fuel) callers (finishCode 13) [.call .chooseLonger [.move (.local 101), .move (.local 102)] 100] wa aa wc ac ∧
      Calling.Prefix (Recursive.original budget fuel) callers (finishCode 15) ((finishActions.drop 13).take 2) wc ac final after ∧
      Calling.Prefix (Recursive.original budget fuel) callers (finishCode 15) ((finishActions.drop 6).take 9) world active final after := by
    intro fuel budget positive
    have args := arguments.noncall_callee (Recursive.original budget fuel) (by decide +kernel)
    have called := stableC fuel budget positive
    have callPrefix : Calling.Prefix (Recursive.original budget fuel) callers (finishCode 13)
        [.call .chooseLonger [.move (.local 101), .move (.local 102)] 100] wa aa wc ac :=
      .cons (Calling.instruction_call_run called) (.nil _ _)
    have last := cleanup.noncall_callee (Recursive.original budget fuel) (by decide +kernel)
    exact ⟨args, called, callPrefix, last, Calling.Prefix.append (suffix := finishCode 15) (rest := (finishActions.drop 12).take 3)
      args (Calling.Prefix.append (suffix := finishCode 15) (rest := (finishActions.drop 13).take 2) callPrefix last)⟩
  have whole := (stable 1 0 (by decide)).2.2.2.2
  have heldFinal : ∀ slot ∈ [71, 85, 95], LocalOwnersAbove before.memory.length final after slot := by
    intro slot member
    have slotBound : slot < prepared.count := by
      change slot < aa.count
      rw [countA, countL, count100, count99]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      omega
    have kept := heldC slot slotBound
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega) ((heldA slot member).prepare_any _)
    exact cleanup.owner_transfer (OwnerTransfer.kept rfl (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide +kernel)) mc.native.valid mc.native.callersValid mc.native.wellFormed kept
  have empty99D : ad.state 99 = .empty :=
    (run100.closed_local_same (index := 99) m99.native.valid m99.native.callersValid m99.native.wellFormed
      (by rw [empty99]; exact .empty .u32) .u32 rfl (by decide)).trans empty99
  have empty99A : aa.state 99 = .empty :=
    (last4.closed_local_same (index := 99) md.native.valid md.native.callersValid md.native.wellFormed
      (by rw [empty99D]; exact .empty .u32) .u32 rfl (by decide)).trans empty99D
  have empty99C : ac.state 99 = .empty := by
    rw [stateC]; simp only [Partial.Locals.set, show (99 : Nat) ≠ 100 by decide, show (99 : Nat) ≠ 102 by decide,
      show (99 : Nat) ≠ 101 by decide, ite_false]
    exact LoanEnding.forget_empty _ _ empty99A
  refine ⟨wa, aa, wc, ac, final, after, machine, ?_, ?_, ?_, ?_, ?_, ?_,
    countAfter.trans (countC.trans (countA.trans (countL.trans (count100.trans count99)))),
    (cleanup.shape.1).trans (frameC.trans (frameA.trans (frameL.trans (frame100.trans frame99)))), ?_, ?_, heldFinal, ?_, ?_, ?_, stable⟩
  · exact (cleanup.closed_local_same (index := 100) mc.native.valid mc.native.callersValid mc.native.wellFormed
      (by rw [stateC]; simp only [Partial.Locals.set, ite_true]; exact ofValue_typed (result_typed _)) (.adt .embedding) rfl (by decide)).trans
        (by rw [stateC]; simp only [Partial.Locals.set, ite_true])
  · have same : aa.state 64 = .empty :=
      (runRight.closed_local_same (index := 64) ml.native.valid ml.native.callersValid ml.native.wellFormed
        (by rw [empty64]; exact .empty .u32) .u32 rfl (by decide)).trans empty64
    have atCall : ac.state 64 = .empty := by
      rw [stateC]
      simp only [Partial.Locals.set, show (64 : Nat) ≠ 100 by decide, show (64 : Nat) ≠ 102 by decide,
        show (64 : Nat) ≠ 101 by decide, ite_false]
      exact LoanEnding.forget_empty _ _ same
    exact (cleanup.closed_local_same (index := 64) mc.native.valid mc.native.callersValid mc.native.wellFormed
      (by rw [atCall]; exact .empty .u32) .u32 rfl (by decide)).trans atCall
  · have atCall : ac.state 81 = .empty := by
      rw [stateC]
      simp only [Partial.Locals.set, show (81 : Nat) ≠ 100 by decide, show (81 : Nat) ≠ 102 by decide,
        show (81 : Nat) ≠ 101 by decide, ite_false]
      exact LoanEnding.forget_empty _ _ empty81
    exact (cleanup.closed_local_same (index := 81) mc.native.valid mc.native.callersValid mc.native.wellFormed
      (by rw [atCall]; exact .empty .u32) .u32 rfl (by decide)).trans atCall
  · exact (cleanup.closed_local_same (index := 99) mc.native.valid mc.native.callersValid mc.native.wellFormed
      (by rw [empty99C]; exact .empty .u32) .u32 rfl (by decide)).trans empty99C
  · exact ⟨b99, by simpa [rootsAfter, rootsC, Activation.forgetRefs, Roots.set] using root99A,
      by rw [memoryAfter]; exact memoryC 99 b99 (by decide) root99A _ raw99A⟩
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [rootsAfter, Roots.set]
  · intro slot outside
    have different : slot ≠ 99 ∧ slot ≠ 100 ∧ slot ≠ 101 ∧ slot ≠ 102 := by simpa using outside
    simp [rootsAfter, rootsC, Activation.forgetRefs, rootsA, rootsL, roots100, roots99, Roots.set,
      different.1, different.2.1, different.2.2.1, different.2.2.2]
  · exact cleanup.owner_transfer (OwnerTransfer.kept rfl (by decide)) mc.native.valid mc.native.callersValid mc.native.wellFormed selectedFresh
  · intro slot outside ty typed closed
    apply whole.closed_local_same_calls typed closed
    have different : slot ≠ 64 ∧ slot ≠ 81 ∧ slot ≠ 99 ∧ slot ≠ 100 ∧ slot ≠ 101 ∧ slot ≠ 102 := by simpa using outside
    simp [finishActions, LocalPreservation.action, LocalPreservation.expression, LocalPreservation.operands, LocalPreservation.operand,
      splitPlace, different.1, different.2.1, different.2.2.1, different.2.2.2.1, different.2.2.2.2.1, different.2.2.2.2.2]
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact whole.retained_local_same_calls (by decide +kernel) (by decide +kernel)
  · intro slot binding root cell read
    have outside : slot ∉ [99, 100, 101, 102] := by intro member; rw [unbound slot member] at root; cases root
    have different : slot ≠ 99 ∧ slot ≠ 100 ∧ slot ≠ 101 ∧ slot ≠ 102 := by simpa using outside
    have root99 : a99.roots slot = some binding := by simpa [roots99, Roots.set, different.1] using root
    have rootD : ad.roots slot = some binding := by simpa [roots100, Roots.set, different.2.1] using root99
    have rootL : al.roots slot = some binding := by simpa [rootsL, Roots.set, different.2.2.1] using rootD
    have rootA : aa.roots slot = some binding := by simpa [rootsA, Roots.set, different.2.2.2] using rootL
    rw [memoryAfter]
    exact memoryC slot binding different.2.1 rootA _ (memoryA slot binding rootL _ (memoryL slot binding rootD _
      (memory100 slot binding root99 _ (memory99 slot binding root cell read))))

end SubtreeProofs.Rust.SourceEval.Evaluator
