module

public import SubtreeProofs.Rust.SourcePairFinishInsertion
public import SubtreeProofs.Rust.SourceOriginalAggregateOne
public import SubtreeProofs.Rust.SourceResultAggregatePrefix

/-! Construct all nine actual parent output assembly instructions. Witness
provenance moves through the optional field into the output tuple; the table
field can transfer original owners independently. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_return_packing_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) (result : CommonEmbedding) (table : MemoTable)
    (selected : active.state 99 = Slot.ofValue (encodeResult result))
    (tableValue : active.state 104 = Slot.ofValue (encodeTable table))
    (above : LocalOwnersAbove before.memory.length world active 99)
    (held : ∀ slot ∈ [71, 85], LocalOwnersAbove before.memory.length world active slot)
    {root0 : Binding} (bound0 : active.roots 0 = some root0)
    (raw0 : world.memory[root0.address]? = some (.node .tuple 0 [])) (empty0 : active.state 0 = .empty)
    (count : 113 ≤ active.count) (unbound : ∀ slot ∈ [110, 111, 112], active.roots slot = none) :
    ∃ (argumentWorld : World) (argumentActive : Activation) (final : World) (after : Activation) (root110 root112 : Binding),
      Calling.Prefix callee callers (finishCode 47) ((finishActions.drop 39).take 8) world active argumentWorld argumentActive ∧
      Calling.Prefix callee callers (finishCode 48) [.assign 0 (.aggregate .tuple 0 [.move (.local 110), .move (.local 112)])]
        argumentWorld argumentActive final after ∧
      Calling.Prefix callee callers (finishCode 48) ((finishActions.drop 39).take 9) world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.state 0 = Slot.ofValue (encodeOutput (some result) table) ∧ LocalResultOwnersAbove before.memory.length final after 0 ∧
      (∀ slot ∈ [99, 104, 110, 111, 112], after.state slot = .empty) ∧
      after.roots 110 = some root110 ∧ after.roots 111 = none ∧ after.roots 112 = some root112 ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [110, 111, 112] → after.roots slot = active.roots slot) ∧
      (∀ slot ∈ [71, 85], LocalOwnersAbove before.memory.length final after slot) ∧
      (∀ slot, slot ∉ [0, 99, 104, 110, 111, 112] →
        (∀ value, active.state slot ≠ .shared value) → after.state slot = active.state slot) ∧
      (∀ slot binding, slot ≠ 0 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  obtain ⟨wo, ao, opened, mo, rootsO, countO, frameO, empty110, raw110, memoryO⟩ :=
    original_open_local_complete h callee (finishCode 40) (slot := 110) (by decide) (by omega) (unbound 110 (by simp))
  have selectedO : ao.state 99 = Slot.ofValue (encodeResult result) :=
    (opened.closed_local_same (index := 99) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [selected]; exact ofValue_typed (result_typed result)) (.adt .embedding) rfl (by decide)).trans selected
  obtain ⟨wl, al, movedWitness, ml, rootsL, countL, frameL, empty99, value111, memoryL⟩ :=
    original_move_view_complete mo callee (finishCode 42) (source := 99) (destination := 111) (by decide) (by decide)
      selectedO (result_typed result) (.adt .embedding) (by rw [countO]; omega)
      (by simpa [rootsO, Roots.set] using unbound 111 (by simp))
  let root110 : Binding := ⟨world.memory.length, world.memory.length⟩
  have bound110L : al.roots 110 = some root110 := by simp [rootsL, rootsO, Roots.set, root110]
  have empty110L : al.state 110 = .empty :=
    (movedWitness.closed_local_same (index := 110) mo.native.valid mo.native.callersValid mo.native.wellFormed
      (by rw [empty110]; exact .empty .u32) .u32 rfl (by decide)).trans empty110
  obtain ⟨ww, aw, wrapped, mw, rootsW, countW, frameW, empty111, option110, memoryW⟩ :=
    original_aggregate_one_complete ml callee (finishCode 43) 111 110 (by decide) (by decide) (by decide)
      (encodeResult result) value111 .optional 1 (option_typed (some result)) (.adt .optional)
      bound110L (memoryL 110 root110 (by simp [rootsO, Roots.set, root110]) _ raw110) empty110L
  have bound111W : aw.roots 111 = some ⟨wo.memory.length, wo.memory.length⟩ := by simp [rootsW, rootsL, Roots.set]
  have plan : RetirementPlan aw.roots ((finishActions.drop 43).take 2) (aw.roots.set 111 none) :=
    .drop bound111W (.dead bound111W (.nil _))
  have zero : ZeroRetirement ((finishActions.drop 43).take 2) aw.state := by
    intro slot member
    have same : slot = 111 := by simpa [finishActions] using member
    subst slot; rw [empty111]; simp only [Slot.dropWork]
  obtain ⟨wr, ar, retired, mr, rootsR, countR, memoryR⟩ := plan.complete_original callee (finishCode 45) mw rfl zero
  have first4 : Calling.Prefix callee callers (finishCode 43) ((finishActions.drop 39).take 4) world active ww aw :=
    Calling.Prefix.append (suffix := finishCode 43) (rest := (finishActions.drop 40).take 3) opened
      (Calling.Prefix.append (suffix := finishCode 43) (rest := [.assign 110 (.aggregate .optional 1 [.move (.local 111)])]) movedWitness wrapped)
  have first6 : Calling.Prefix callee callers (finishCode 45) ((finishActions.drop 39).take 6) world active wr ar :=
    Calling.Prefix.append (suffix := finishCode 45) (rest := (finishActions.drop 43).take 2) first4 retired
  have tableR : ar.state 104 = Slot.ofValue (encodeTable table) :=
    (first6.closed_local_same (index := 104) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [tableValue]; exact ofValue_typed (table_typed table)) (.adt .table) rfl (by decide +kernel)).trans tableValue
  obtain ⟨wa, aa, movedTable, ma, rootsA, countA, frameA, empty104, value112, memoryA⟩ :=
    original_move_view_complete mr callee (finishCode 47) (source := 104) (destination := 112) (by decide) (by decide)
      tableR (table_typed table) (.adt .table) (by rw [countR, countW, countL, countO]; omega)
      (by simpa [rootsR, rootsW, rootsL, rootsO, Roots.set] using unbound 112 (by simp))
  have first8 : Calling.Prefix callee callers (finishCode 47) ((finishActions.drop 39).take 8) world active wa aa :=
    Calling.Prefix.append (suffix := finishCode 47) (rest := (finishActions.drop 45).take 2) first6 movedTable
  have tail4 : Calling.Prefix callee callers (finishCode 47) ((finishActions.drop 43).take 4) ww aw wa aa :=
    Calling.Prefix.append (suffix := finishCode 47) (rest := (finishActions.drop 45).take 2) retired movedTable
  have optionA : aa.state 110 = Slot.ofValue (encodeOption (some result)) :=
    (tail4.closed_local_same (index := 110) mw.native.valid mw.native.callersValid mw.native.wellFormed
      (by rw [option110]; exact ofValue_typed (option_typed (some result))) (.adt .optional) rfl (by decide +kernel)).trans option110
  have root0O : ao.roots 0 = some root0 := by simpa [rootsO, Roots.set] using bound0
  have root0L : al.roots 0 = some root0 := by simpa [rootsL, Roots.set] using root0O
  have root0W : aw.roots 0 = some root0 := by rw [rootsW]; exact root0L
  have root0R : ar.roots 0 = some root0 := by simpa [rootsR, Roots.set] using root0W
  have root0A : aa.roots 0 = some root0 := by simpa [rootsA, Roots.set] using root0R
  have raw0O := memoryO 0 root0 bound0 _ raw0
  have raw0L := memoryL 0 root0 root0O _ raw0O
  have raw0W := memoryW 0 root0 (by decide) root0L _ raw0L
  have raw0R : wr.memory[root0.address]? = some (.node .tuple 0 []) := by rw [memoryR]; exact raw0W
  have raw0A := memoryA 0 root0 root0R _ raw0R
  have empty0A : aa.state 0 = .empty :=
    (first8.closed_local_same (index := 0) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [empty0]; exact .empty .u32) .u32 rfl (by decide +kernel)).trans empty0
  obtain ⟨final, after, assigned, machine, rootsAfter, countAfter, frameAfter, empty110After, empty112After, output, kept, memoryAfter⟩ :=
    original_aggregate_two_complete ma callee (finishCode 48) 110 112 0 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (encodeOption (some result)) (encodeTable table) optionA value112
      .tuple 0 (encodeOutput_typed (some result) table) (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil)))
      root0A raw0A empty0A
  have whole : Calling.Prefix callee callers (finishCode 48) ((finishActions.drop 39).take 9) world active final after :=
    Calling.Prefix.append (suffix := finishCode 48) (rest := [.assign 0 (.aggregate .tuple 0 [.move (.local 110), .move (.local 112)])]) first8 assigned
  have transfer : OwnerTransfer 99 ((finishActions.drop 39).take 8) 110 :=
    .keep rfl (by decide) (.keep rfl (by decide)
      (.assign (fun _ _ _ fresh => OperandSourcesAbove.single_move fresh rfl)
        (.assign (fun _ _ _ fresh => OperandSourcesAbove.single_move fresh rfl)
          (.keep rfl (by decide) (.keep rfl (by decide) (.keep rfl (by decide) (.keep rfl (by decide) (.nil 110))))))))
  have optionFresh := first8.owner_transfer transfer h.native.valid h.native.callersValid h.native.wellFormed above
  have resultFresh := assigned.aggregate_result_owner_provenance ma.native.valid optionFresh
  have empty99A : aa.state 99 = .empty := by
    have tail5 : Calling.Prefix callee callers (finishCode 47) ((finishActions.drop 42).take 5) wl al wa aa :=
      Calling.Prefix.append (suffix := finishCode 47) (rest := (finishActions.drop 43).take 4) wrapped tail4
    exact (tail5.closed_local_same (index := 99) ml.native.valid ml.native.callersValid ml.native.wellFormed
      (by rw [empty99]; exact .empty .u32) .u32 rfl (by decide +kernel)).trans empty99
  refine ⟨wa, aa, final, after, root110, ⟨wr.memory.length, wr.memory.length⟩, first8, assigned, whole, machine,
    output, resultFresh, ?_, ?_, ?_, ?_, countAfter.trans (countA.trans (countR.trans (countW.trans (countL.trans countO)))) ,
    frameAfter.trans (frameA.trans (retired.shape.1.trans (frameW.trans (frameL.trans frameO)))), ?_, ?_, ?_, ?_⟩
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact (kept 99 (by decide) (by decide) (by decide) .u32 (by rw [empty99A]; exact .empty _) .u32).trans empty99A
    · exact (kept 104 (by decide) (by decide) (by decide) .u32 (by rw [empty104]; exact .empty _) .u32).trans empty104
    · exact empty110After
    · obtain ⟨_, frame⟩ := machine.native.valid.2
      have rootNone : after.roots 111 = none := by simp [rootsAfter, rootsA, rootsR, Roots.set]
      have mask := frame.slots 111
      change (match after.roots 111 with | none => after.state 111 = .empty | some binding => _) at mask
      simpa only [rootNone] using mask
    · exact empty112After
  · simp [rootsAfter, rootsA, rootsR, rootsW, rootsL, rootsO, Roots.set, root110]
  · simp [rootsAfter, rootsA, rootsR, Roots.set]
  · simp [rootsAfter, rootsA, Roots.set]
  · intro slot outside
    have different : slot ≠ 110 ∧ slot ≠ 111 ∧ slot ≠ 112 := by simpa using outside
    simp [rootsAfter, rootsA, rootsR, rootsW, rootsL, rootsO, Roots.set, different.1, different.2.1, different.2.2]
  · intro slot member
    exact whole.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> decide +kernel)) h.native.valid h.native.callersValid h.native.wellFormed (held slot member)
  · intro slot outside unshared
    apply whole.unshared_local_same h.native.valid h.native.callersValid h.native.wellFormed unshared (by decide +kernel)
    have different : slot ≠ 0 ∧ slot ≠ 99 ∧ slot ≠ 104 ∧ slot ≠ 110 ∧ slot ≠ 111 ∧ slot ≠ 112 := by simpa using outside
    simp [finishActions, SourceEval.LocalPreservation.action, SourceEval.LocalPreservation.expression,
      SourceEval.LocalPreservation.operands, SourceEval.LocalPreservation.operand, splitPlace,
      different.1, different.2.1, different.2.2.1, different.2.2.2.1, different.2.2.2.2.1, different.2.2.2.2.2]
  · intro slot binding other0 root raw read
    have outside : slot ∉ [110, 111, 112] := by intro member; rw [unbound slot member] at root; cases root
    have different : slot ≠ 110 ∧ slot ≠ 111 ∧ slot ≠ 112 := by simpa using outside
    have rootO : ao.roots slot = some binding := by simpa [rootsO, Roots.set, different.1] using root
    have rootL : al.roots slot = some binding := by simpa [rootsL, Roots.set, different.2.1] using rootO
    have rootW : aw.roots slot = some binding := by rw [rootsW]; exact rootL
    have rootR : ar.roots slot = some binding := by simpa [rootsR, Roots.set, different.2.1] using rootW
    have rootA : aa.roots slot = some binding := by simpa [rootsA, Roots.set, different.2.2] using rootR
    have rawW := memoryW slot binding different.1 rootL raw (memoryL slot binding rootO raw (memoryO slot binding root raw read))
    exact memoryAfter slot binding other0 rootA raw (memoryA slot binding rootR raw (by rw [memoryR]; exact rawW))

end SubtreeProofs.Rust.SourceEval.Evaluator
