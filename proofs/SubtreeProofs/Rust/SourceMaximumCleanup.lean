module

public import SubtreeProofs.Rust.SourceMaximumResultTransfer
public import SubtreeProofs.Rust.SourceOriginalOwnedDrop
public import SubtreeProofs.Rust.SourceOriginalRetirement
public import SubtreeProofs.Rust.SourceReturnTotality

/-! Construct all eight public cleanup actions and return. The updated table
is destroyed from its real remaining partial tuple after the option transfer;
whole-packet cold provenance derives its loan permission and owner retirement. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Maximum

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem cleanup_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [5, 4, 1, 2] world active)
    (callee : Derived.Callees) (count : active.count = 7)
    {result : Option CommonEmbedding} {table : MemoTable}
    (output : active.state 3 = Slot.ofValue (Evaluator.encodeOutput result table))
    (above : LocalOwnersAbove before.memory.length world active 3)
    {root0 root1 root2 root3 root4 root5 root6 : Binding}
    (bound0 : active.roots 0 = some root0) (bound1 : active.roots 1 = some root1)
    (bound2 : active.roots 2 = some root2) (bound3 : active.roots 3 = some root3)
    (bound4 : active.roots 4 = some root4) (bound5 : active.roots 5 = some root5)
    (bound6 : active.roots 6 = some root6)
    (raw0 : world.memory[root0.address]? = some (.node .tuple 0 [])) (empty0 : active.state 0 = .empty)
    (emptyArgs : ∀ slot ∈ [4, 5, 6], active.state slot = .empty) :
    ∃ final after cell work,
      Calling.exec callee callers (afterCall.foldr Control.Tree.step .ret) world active =
        some (.returned final after (cell, encodeOption result), work) ∧
      (∀ slot, after.state slot = .empty) ∧ after.RootsSeparate callers ∧
      (∀ slot binding, after.roots slot = some binding → before.memory.length ≤ binding.address) ∧
      Preserves before final previous.reads := by
  let retiredRoots := ((active.roots.set 6 none).set 5 none).set 4 none
  have plan : RetirementPlan active.roots [.storageDead 6, .storageDead 5, .storageDead 4] retiredRoots :=
    .dead bound6 (.dead (binding := root5) (by simpa [Roots.set] using bound5)
      (.dead (binding := root4) (by simpa [Roots.set] using bound4) (.nil _)))
  have zero : ZeroRetirement [.storageDead 6, .storageDead 5, .storageDead 4] active.state := by
    intro slot member
    have arg : slot ∈ [4, 5, 6] := by simp at member ⊢; tauto
    rw [emptyArgs slot arg]; simp only [Slot.dropWork]
  obtain ⟨wr, ar, retired, mr, rootsR, countR, memoryR⟩ := plan.complete_original callee (cleanupCode 3) h rfl zero
  have outputR : ar.state 3 = Slot.ofValue (Evaluator.encodeOutput result table) :=
    (retired.closed_local_same_calls (index := 3)
      (by rw [output]; exact ofValue_typed (Evaluator.encodeOutput_typed result table))
      (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (by decide)).trans output
  have freshR := LocalOwnersAbove.memory_same (after := ar) h.native.valid above memoryR
    (by simp [rootsR, retiredRoots, Roots.set]) (by rw [outputR, output])
  have returnR : ar.roots 0 = some root0 := by simpa [rootsR, retiredRoots, Roots.set] using bound0
  have resultR : ar.roots 3 = some root3 := by simpa [rootsR, retiredRoots, Roots.set] using bound3
  have oneR : ar.roots 1 = some root1 := by simpa [rootsR, retiredRoots, Roots.set] using bound1
  have twoR : ar.roots 2 = some root2 := by simpa [rootsR, retiredRoots, Roots.set] using bound2
  obtain ⟨wt, aT, transfer, mt, rootsT, countT, frameT, optionT, tableT, freshT, _⟩ :=
    result_transfer_complete mr callee (by omega) outputR freshR returnR
      (by rw [memoryR]; exact raw0) (retired.empty_untouched empty0 (by decide))
  let prepared := aT.forgetRefs (cleanupCode 4)
  have mp := mt.prepare (cleanupCode 4)
  have resultP : prepared.roots 3 = some root3 := by rw [show prepared.roots = aT.roots from rfl, rootsT]; exact resultR
  obtain ⟨discarded, dropped, length, md⟩ := mp.drop_fresh resultP
    (by intro index member; change index < aT.count; rw [countT, countR, count]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega)
    (freshT.prepare_any (cleanupCode 4))
  let wd := wt.retire discarded
  let ad : Activation := {prepared with state := prepared.state.set 3 .empty}
  change OriginalLoanMachine before callers previous external [5, 4, 1, 2] wd ad at md
  have dropSteps : Calling.Prefix callee callers (cleanupCode 5) [.drop 3] wt aT wd ad :=
    .cons (Calling.instruction_noncall_run (act := .drop 3) dropped) (.nil _ _)
  have returnD : ad.roots 0 = some root0 := by change aT.roots 0 = _; rw [rootsT]; exact returnR
  have resultD : ad.roots 3 = some root3 := resultP
  have oneD : ad.roots 1 = some root1 := by change aT.roots 1 = _; rw [rootsT]; exact oneR
  have twoD : ad.roots 2 = some root2 := by change aT.roots 2 = _; rw [rootsT]; exact twoR
  have lastPlan : RetirementPlan ad.roots [.storageDead 3, .storageDead 2, .storageDead 1]
      (((ad.roots.set 3 none).set 2 none).set 1 none) :=
    .dead resultD (.dead (binding := root2) (by simpa [Roots.set] using twoD)
      (.dead (binding := root1) (by simpa [Roots.set] using oneD) (.nil _)))
  have lastZero : ZeroRetirement [.storageDead 3, .storageDead 2, .storageDead 1] ad.state := by
    intro slot member
    have selected : slot = 3 ∨ slot = 2 ∨ slot = 1 := by simp at member; tauto
    rcases selected with rfl | rfl | rfl
    · simp only [ad, Partial.Locals.set, ite_true, Slot.dropWork]
    · exact md.zero 2 (by simp)
    · exact md.zero 1 (by simp)
  obtain ⟨final, current, ended, machine, rootsE, _, _⟩ := lastPlan.complete_original callee .ret md rfl lastZero
  have returnE : current.roots 0 = some root0 := by simpa [rootsE, Roots.set] using returnD
  have optionD : ad.state 0 = Slot.ofValue (encodeOption result) :=
    (dropSteps.closed_local_same_calls (index := 0) (by rw [optionT]; exact ofValue_typed (option_typed result))
      (.adt .optional) (by decide)).trans optionT
  have optionE : current.state 0 = Slot.ofValue (encodeOption result) :=
    (ended.closed_local_same_calls (index := 0) (by rw [optionD]; exact ofValue_typed (option_typed result))
      (.adt .optional) (by decide)).trans optionD
  have others : ∀ slot, slot ≠ 0 → current.state slot = .empty := by
    intro slot nonzero
    have unbound : current.roots slot = none := by
      rw [rootsE]
      change (((aT.roots.set 3 none).set 2 none).set 1 none) slot = none
      rw [rootsT, rootsR]
      change ((((((active.roots.set 6 none).set 5 none).set 4 none).set 3 none).set 2 none).set 1 none) slot = none
      by_cases one : slot = 1
      · subst slot; simp [Roots.set]
      by_cases two : slot = 2
      · subst slot; simp [Roots.set]
      by_cases three : slot = 3
      · subst slot; simp [Roots.set]
      by_cases four : slot = 4
      · subst slot; simp [Roots.set]
      by_cases five : slot = 5
      · subst slot; simp [Roots.set]
      by_cases six : slot = 6
      · subst slot; simp [Roots.set]
      simp only [Roots.set, one, two, three, four, five, six, ite_false]
      exact h.native.valid.1 slot (by rw [count]; omega)
    obtain ⟨_, frame⟩ := machine.native.valid.2
    simpa only [unbound] using frame.slots slot
  have closed : ClosedState current.state := by
    intro slot
    by_cases zero : slot = 0
    · subst slot; exact ⟨.adt .optional, by rw [optionE]; exact ofValue_typed (option_typed result), .adt .optional⟩
    · exact ⟨.u32, by rw [others slot zero]; exact .empty _, .u32⟩
  have loans := Derived.ReturnLoansAllowed.of_closed_preserved (fun slot _ => closed slot)
    h.native.previousCallers h.native.beforeWellFormed machine.native.kept (machine.native.fresh 0 root0 returnE)
  obtain ⟨cell, returned⟩ := Derived.returnValue_complete machine.native.valid machine.native.callersValid
    machine.native.separate machine.native.ownerFrame returnE
    (by rw [optionE]; exact Slot.materialize_ofValue _) loans
  have last4 : Calling.Prefix callee callers .ret (afterCall.drop 4) wt aT final current :=
    Calling.Prefix.append (suffix := .ret) (rest := afterCall.drop 5) dropSteps ended
  have last5 : Calling.Prefix callee callers .ret (afterCall.drop 3) wr ar final current :=
    Calling.Prefix.append (suffix := .ret) (rest := afterCall.drop 4) transfer last4
  have whole : Calling.Prefix callee callers .ret afterCall world active final current :=
    Calling.Prefix.append (suffix := .ret) (rest := afterCall.drop 3) retired last5
  obtain ⟨work, run⟩ := whole.exec returned
  refine ⟨final, {current with state := current.state.set 0 .empty}, cell, work, run, ?_, machine.native.separate,
    machine.native.fresh, machine.native.kept⟩
  intro slot
  by_cases zero : slot = 0
  · subst slot; simp only [Partial.Locals.set, ite_true]
  · simpa only [Partial.Locals.set, zero, ite_false] using others slot zero

end SubtreeProofs.Rust.SourceEval.Maximum
