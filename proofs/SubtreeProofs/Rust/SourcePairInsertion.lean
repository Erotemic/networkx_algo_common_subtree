module

public import SubtreeProofs.Rust.SourcePairInsertCall

/-! The complete actual insertion region, including all argument construction,
the native helper call and physical retirement, reaches output assembly. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_insertion_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (left right : BalancedWord) (table : MemoTable) (result : CommonEmbedding)
    (query1 : active.state 1 = .shared (encodeWord left)) (query2 : active.state 2 = .shared (encodeWord right))
    (tableValue : active.state 89 = Slot.ofValue (encodeTable table))
    (selected : active.state 99 = Slot.ofValue (encodeResult result))
    (heldAbove : ∀ slot ∈ [71, 85, 99], LocalOwnersAbove before.memory.length world active slot)
    (count : 110 ≤ active.count) (unbound : ∀ slot ∈ [104, 105, 106, 107, 108, 109], active.roots slot = none) :
    ∃ minimumFuel minimumBudget argumentWorld argumentActive callWorld callActive final after cost,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.state 104 = Slot.ofValue (encodeTable (.Entry ⟨left, right, result⟩ table)) ∧
      after.state 99 = Slot.ofValue (encodeResult result) ∧ after.state 89 = .empty ∧
      (∀ slot ∈ [105, 106, 107, 108, 109], after.state slot = .empty ∧ after.roots slot = none) ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [104, 105, 106, 107, 108, 109] → after.roots slot = active.roots slot) ∧
      (∀ slot ∈ [71, 85, 99], LocalOwnersAbove before.memory.length final after slot) ∧
      (∀ slot, slot ∉ [89, 104, 105, 106, 107, 108, 109] →
        (∀ value, active.state slot ≠ .shared value) → after.state slot = active.state slot) ∧
      (∀ slot binding, active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 32) ((finishActions.drop 21).take 11)
          world active argumentWorld argumentActive ∧
        Derived.call (Recursive.original budget fuel) argumentWorld (argumentActive.forgetRefs (finishCode 32)) callers
          .insert pairInsertArgs 104 = some (callWorld, callActive, cost) ∧
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 39) ((finishActions.drop 33).take 6)
          callWorld callActive final after ∧
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 39) ((finishActions.drop 21).take 18)
          world active final after := by
  let callee := Helpers.callee 0 0
  obtain ⟨ws, aS, setup, ms, countS, frameS, empty89, table105, view106, view107, emptyRoots, rootsOutside, freshS, sameS, memoryS⟩ :=
    pair_insert_setup_complete h callee left right table query1 query2 tableValue heldAbove count unbound
  have selectedS : aS.state 99 = Slot.ofValue (encodeResult result) :=
    (sameS 99 (by decide) (by
        intro value same
        have typed : SlotTyped (active.state 99) (.adt .embedding) := by rw [selected]; exact ofValue_typed (result_typed result)
        rw [same] at typed
        cases typed)).trans selected
  obtain ⟨empty108, b108, bound108, raw108⟩ := emptyRoots 108 (by simp)
  obtain ⟨empty109, b109, bound109, raw109⟩ := emptyRoots 109 (by simp)
  obtain ⟨empty104, b104, bound104, raw104⟩ := emptyRoots 104 (by simp)
  obtain ⟨wa, aa, views, ma, rootsA, countA, frameA, value108, value109, originsA, zerosA, closedA, mixedA, freshA, queriesA, sameA, memoryA⟩ :=
    pair_insert_views_complete ms callee result selectedS (by decide) (by decide) bound108 bound109 empty108 empty109 raw108 raw109 freshS
  have tableA : aa.state 105 = Slot.ofValue (encodeTable table) :=
    (sameA 105 (by decide) (by decide) (by
        intro value same
        have typed : SlotTyped (aS.state 105) (.adt .table) := by rw [table105]; exact ofValue_typed (table_typed table)
        rw [same] at typed
        cases typed)).trans table105
  have empty104A : aa.state 104 = .empty :=
    (sameA 104 (by decide) (by decide) (by rw [empty104]; intro value same; cases same)).trans empty104
  have arguments : Calling.Prefix callee callers (finishCode 32) ((finishActions.drop 21).take 11) world active wa aa :=
    Calling.Prefix.append (suffix := finishCode 32) (rest := (finishActions.drop 30).take 2) setup views
  obtain ⟨minFuel, minBudget, wc, ac, cost, mc, rootsC, countC, frameC, stateC, tableC, emptyC, freshC, sameC, memoryC, stableC⟩ :=
    pair_insert_call_complete ma mixedA closedA
      (by intro slot member; exact originsA slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto))
      (by intro slot member; exact zerosA slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto))
      left right table result tableA ((queriesA 106 (by simp)).trans view106) ((queriesA 107 (by simp)).trans view107)
      value108 value109 (by rw [rootsA]; exact bound104) empty104A
      (memoryA 104 b104 (by decide) (by decide) bound104 _ raw104) freshA (by rw [countA, countS]; exact count)
  obtain ⟨b105, bound105⟩ := Activation.root_of_materialize ma.valid (value := encodeTable table)
    (by rw [tableA]; exact Slot.materialize_ofValue _)
  obtain ⟨b106, bound106⟩ := Activation.root_of_materialize ma.valid (value := .reference (encodeWord left))
    (by rw [(queriesA 106 (by simp)).trans view106]; simp only [Slot.materialize])
  obtain ⟨b107, bound107⟩ := Activation.root_of_materialize ma.valid (value := .reference (encodeWord right))
    (by rw [(queriesA 107 (by simp)).trans view107]; simp only [Slot.materialize])
  have plan4 : RetirementPlan ac.roots ((finishActions.drop 33).take 4)
      ((((ac.roots.set 108 none).set 107 none).set 106 none).set 105 none) :=
    .dead (by rw [rootsC, rootsA]; exact bound108)
      (.dead (by simpa [Roots.set, rootsC] using bound107)
        (.dead (by simpa [Roots.set, rootsC] using bound106)
          (.dead (by simpa [Roots.set, rootsC] using bound105) (.nil _))))
  have zero4 : ZeroRetirement ((finishActions.drop 33).take 4) ac.state := by
    intro slot member
    have temporary : slot ∈ [105, 106, 107, 108, 109] := by
      simp only [finishActions, List.drop, List.take, List.mem_cons, List.not_mem_nil, or_false, SourceEval.Action.storageDead.injEq, reduceCtorEq] at member ⊢
      tauto
    rw [emptyC slot temporary]; simp only [Slot.dropWork]
  obtain ⟨wr, ar, retire4, mr, rootsR, countR, memoryR⟩ := plan4.complete_original callee (finishCode 37) mc rfl zero4
  let observed := ar.forgetRefs (finishCode 37)
  have observedMachine := mr.prepare (finishCode 37)
  have fake : Calling.Prefix callee callers (finishCode 38) [.fakeRead (.local 104)] wr ar wr observed :=
    .cons (Calling.instruction_noncall_run (act := .fakeRead (.local 104)) rfl) (.nil _ _)
  have empty109R : ar.state 109 = .empty :=
    (retire4.closed_local_same (index := 109) mc.native.valid mc.native.callersValid mc.native.wellFormed
      (by rw [emptyC 109 (by simp)]; exact .empty .u32) .u32 rfl (by decide +kernel)).trans (emptyC 109 (by simp))
  have plan1 : RetirementPlan observed.roots [.storageDead 109] (observed.roots.set 109 none) :=
    .dead (by change ar.roots 109 = some b109; rw [rootsR]; simpa [Roots.set, rootsC, rootsA] using bound109) (.nil _)
  obtain ⟨final, after, retire1, machine, rootsAfter, countAfter, memoryAfter⟩ := plan1.complete_original callee (finishCode 39) observedMachine rfl
    (by intro slot member
        have same : slot = 109 := by simpa using member
        subst slot
        have empty : observed.state 109 = .empty := LoanEnding.forget_empty (finishCode 37) (List.range ar.count) empty109R
        rw [empty]; simp only [Slot.dropWork])
  have cleanup : Calling.Prefix callee callers (finishCode 39) ((finishActions.drop 33).take 6) wc ac final after :=
    Calling.Prefix.append (suffix := finishCode 39) (rest := (finishActions.drop 37).take 2) retire4
      (Calling.Prefix.append (suffix := finishCode 39) (rest := [.storageDead 109]) fake retire1)
  have stable : ∀ fuel budget, minFuel ≤ fuel → minBudget ≤ budget →
      Calling.Prefix (Recursive.original budget fuel) callers (finishCode 32) ((finishActions.drop 21).take 11) world active wa aa ∧
      Derived.call (Recursive.original budget fuel) wa (aa.forgetRefs (finishCode 32)) callers .insert pairInsertArgs 104 = some (wc, ac, cost) ∧
      Calling.Prefix (Recursive.original budget fuel) callers (finishCode 39) ((finishActions.drop 33).take 6) wc ac final after ∧
      Calling.Prefix (Recursive.original budget fuel) callers (finishCode 39) ((finishActions.drop 21).take 18) world active final after := by
    intro fuel budget hf hb
    have first := arguments.noncall_callee (Recursive.original budget fuel) (by decide +kernel)
    obtain ⟨called, callPrefix⟩ := stableC fuel budget hf hb
    have last := cleanup.noncall_callee (Recursive.original budget fuel) (by decide +kernel)
    exact ⟨first, called, last, Calling.Prefix.append (suffix := finishCode 39) (rest := (finishActions.drop 32).take 7) first
      (Calling.Prefix.append (suffix := finishCode 39) (rest := (finishActions.drop 33).take 6) callPrefix last)⟩
  have whole := (stable minFuel minBudget (by rfl) (by rfl)).2.2.2
  have rootShape : ∀ slot, slot ∉ [104, 105, 106, 107, 108, 109] → after.roots slot = active.roots slot := by
    intro slot outside
    have different : slot ≠ 104 ∧ slot ≠ 105 ∧ slot ≠ 106 ∧ slot ≠ 107 ∧ slot ≠ 108 ∧ slot ≠ 109 := by simpa using outside
    simp only [rootsAfter, observed, Activation.forgetRefs, rootsR, Roots.set, different.2.1, different.2.2.1,
      different.2.2.2.1, different.2.2.2.2.1, different.2.2.2.2.2, ite_false, rootsC, rootsA]
    exact rootsOutside slot outside
  refine ⟨minFuel, minBudget, wa, aa, wc, ac, final, after, cost, machine, ?_, ?_, ?_, ?_,
    countAfter.trans (countR.trans (countC.trans (countA.trans countS))),
    cleanup.shape.1.trans (frameC.trans (frameA.trans frameS)), rootShape, ?_, ?_, ?_, stable⟩
  · exact (cleanup.closed_local_same (index := 104) mc.native.valid mc.native.callersValid mc.native.wellFormed
      (by rw [tableC]; exact ofValue_typed (table_typed _)) (.adt .table) rfl (by decide +kernel)).trans tableC
  · exact (whole.closed_local_same_calls (by rw [selected]; exact ofValue_typed (result_typed result)) (.adt .embedding) (by decide +kernel)).trans selected
  · have empty89A : aa.state 89 = .empty :=
      (sameA 89 (by decide) (by decide) (by rw [empty89]; intro value same; cases same)).trans empty89
    have prepared89 : (aa.forgetRefs (finishCode 32)).state 89 = aa.state 89 :=
      (LoanEnding.forget_empty (finishCode 32) (List.range aa.count) empty89A).trans empty89A.symm
    have empty89C : ac.state 89 = .empty := (sameC 89 (by decide) prepared89).trans empty89A
    exact (cleanup.closed_local_same (index := 89) mc.native.valid mc.native.callersValid mc.native.wellFormed
      (by rw [empty89C]; exact .empty .u32) .u32 rfl (by decide +kernel)).trans empty89C
  · intro slot member
    refine ⟨?_, ?_⟩
    · obtain ⟨_, frame⟩ := machine.native.valid.2
      have rootNone : after.roots slot = none := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [rootsAfter, observed, Activation.forgetRefs, rootsR, Roots.set]
      have mask := frame.slots slot
      change (match after.roots slot with | none => after.state slot = .empty | some binding => _) at mask
      simpa only [rootNone] using mask
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [rootsAfter, observed, Activation.forgetRefs, rootsR, Roots.set]
  · intro slot member
    exact cleanup.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide +kernel)) mc.native.valid mc.native.callersValid mc.native.wellFormed (freshC slot member)
  · intro slot outside unshared
    apply whole.unshared_local_same_calls unshared
    have different : slot ≠ 89 ∧ slot ≠ 104 ∧ slot ≠ 105 ∧ slot ≠ 106 ∧ slot ≠ 107 ∧ slot ≠ 108 ∧ slot ≠ 109 := by simpa using outside
    simp [finishActions, SourceEval.LocalPreservation.action, SourceEval.LocalPreservation.expression,
      SourceEval.LocalPreservation.operands, SourceEval.LocalPreservation.operand, splitPlace,
      different.1, different.2.1, different.2.2.1, different.2.2.2.1, different.2.2.2.2.1, different.2.2.2.2.2.1, different.2.2.2.2.2.2]
  · intro slot binding root raw read
    have outside : slot ∉ [104, 105, 106, 107, 108, 109] := by intro member; rw [unbound slot member] at root; cases root
    have different : slot ≠ 104 ∧ slot ≠ 105 ∧ slot ≠ 106 ∧ slot ≠ 107 ∧ slot ≠ 108 ∧ slot ≠ 109 := by simpa using outside
    have rootS : aS.roots slot = some binding := by rw [rootsOutside slot outside]; exact root
    have rootA : aa.roots slot = some binding := by rw [rootsA]; exact rootS
    rw [memoryAfter, memoryR]
    exact memoryC slot binding different.1 rootA raw (memoryA slot binding different.2.2.2.2.1 different.2.2.2.2.2 rootS raw (memoryS slot binding root raw read))

end SubtreeProofs.Rust.SourceEval.Evaluator
