module

public import SubtreeProofs.Rust.SourcePairReturnRetirement

/-! Successful right payload, both choices, insertion, output assembly and the
first eight zero-owner cleanup instructions reach the remaining parent cleanup.
The original empty return root is an explicit pre-region storage invariant. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

structure FinishPackedScope (lh lt rh rt : BalancedWord) (heads tails left right : CommonEmbedding)
    (table : MemoTable) (total : Aeneas.Std.U32) (active : Activation) : Prop where
  tuple : active.state 13 = queryTuple (.Pair lh lt) (.Pair rh rt)
  endedViews : ∀ slot ∈ [27, 28, 29, 30], active.state slot = .empty
  headHole : active.state 37 = resultWordHole heads.edges
  tailHole : active.state 47 = resultWordHole tails.edges
  totalValue : active.state 58 = .number total.val
  leftWord : active.state 71 = Slot.ofValue (encodeWord (OrderedSolver.appendWord lh lt))
  leftHole : active.state 74 = headPayloadHole
  rightWord : active.state 85 = Slot.ofValue (encodeWord (OrderedSolver.appendWord rh rt))
  rightHole : active.state 88 = headPayloadHole
  headTableEmpty : active.state 42 = .empty
  leftTableEmpty : active.state 75 = .empty
  output : active.state 0 = Slot.ofValue (encodeOutput
    (some (selectedWitness (matchedWitness heads tails total) left right))
    (.Entry ⟨.Pair lh lt, .Pair rh rt, selectedWitness (matchedWitness heads tails total) left right⟩ table))
  moved : ∀ slot ∈ [64, 81, 89, 95, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112], active.state slot = .empty
  retired : ∀ slot ∈ [65, 70, 86, 87, 90, 91, 92, 93, 94, 96, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112], active.roots slot = none

theorem pair_finish_packing_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {lh lt rh rt : BalancedWord} {heads tails left right : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : PairRightScope lh lt rh rt heads tails left total (some right) table world active)
    (above : LocalOwnersAbove before.memory.length world active 88)
    (heldAbove : ∀ slot ∈ [64, 71, 81, 85], LocalOwnersAbove before.memory.length world active slot)
    {root0 : Binding} (bound0 : active.roots 0 = some root0)
    (raw0 : world.memory[root0.address]? = some (.node .tuple 0 [])) (empty0 : active.state 0 = .empty)
    (count : 113 ≤ active.count) (unbound : ∀ slot ∈ [96, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112], active.roots slot = none) :
    ∃ (minimumFuel minimumBudget : Nat) (insertionWorld : World) (insertionActive : Activation)
        (argumentWorld : World) (argumentActive : Activation) (packedWorld : World) (packedActive : Activation) (final : World) (after : Activation),
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      FinishPackedScope lh lt rh rt heads tails left right table total after ∧
      LocalResultOwnersAbove before.memory.length final after 0 ∧
      (∀ slot ∈ [71, 85], LocalOwnersAbove before.memory.length final after slot) ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112] → after.roots slot = active.roots slot) ∧
      (∀ slot binding, slot ≠ 0 → slot ≠ 95 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 39) (finishActions.take 39) world active insertionWorld insertionActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 47) ((finishActions.drop 39).take 8) insertionWorld insertionActive argumentWorld argumentActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 48) [.assign 0 (.aggregate .tuple 0 [.move (.local 110), .move (.local 112)])]
          argumentWorld argumentActive packedWorld packedActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 56) ((finishActions.drop 48).take 8) packedWorld packedActive final after ∧
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 56) (finishActions.take 56) world active final after := by
  let callee := Helpers.callee 0 0
  obtain ⟨minFuel, minBudget, _, _, _, _, _, _, wi, ai, _, mi, insertionScope, freshI, countI, frameI, rootsI, memoryI, stableI⟩ :=
    pair_finish_insertion_complete h scope above heldAbove (by omega)
      (by intro slot member; exact unbound slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; omega))
  have prefixI := (stableI minFuel minBudget (by rfl) (by rfl)).2.2.2.2.2
  have bound0I : ai.roots 0 = some root0 := by rw [rootsI 0 (by decide)]; exact bound0
  have empty0I : ai.state 0 = .empty :=
    (prefixI.closed_local_same_calls (index := 0) (by rw [empty0]; exact .empty .u32) .u32 (by decide +kernel)).trans empty0
  obtain ⟨wa, aa, wp, ap, root110, root112, args, assign0, packing, mp, outputP, freshP, emptyP, root110P, dead111P, root112P,
    countP, frameP, rootsP, heldP, sameP, memoryP⟩ := pair_return_packing_complete mi callee
      (selectedWitness (matchedWitness heads tails total) left right)
      (.Entry ⟨.Pair lh lt, .Pair rh rt, selectedWitness (matchedWitness heads tails total) left right⟩ table)
      insertionScope.selected insertionScope.tableValue (freshI 99 (by simp))
      (by intro slot member; exact freshI slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; omega))
      bound0I (memoryI 0 root0 (by decide) bound0 _ raw0) empty0I (by rw [countI]; exact count)
      (by intro slot member
          have outside : slot ∉ [99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109] := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; omega
          rw [rootsI slot outside]
          exact unbound slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; omega))
  obtain ⟨root99, bound99⟩ := Activation.root_of_materialize mi.native.valid (value := encodeResult (selectedWitness (matchedWitness heads tails total) left right))
    (by rw [insertionScope.selected]; exact Slot.materialize_ofValue _)
  obtain ⟨root104, bound104⟩ := Activation.root_of_materialize mi.native.valid
    (value := encodeTable (.Entry ⟨.Pair lh lt, .Pair rh rt, selectedWitness (matchedWitness heads tails total) left right⟩ table))
    (by rw [insertionScope.tableValue]; exact Slot.materialize_ofValue _)
  obtain ⟨final, after, cleanup, machine, outputAfter, freshAfter, retiredAfter, countAfter, frameAfter, memoryAfter, rootsAfter, heldAfter, sameAfter⟩ :=
    pair_return_retirement_complete mp callee _ _ outputP freshP
      (by intro slot member; exact emptyP slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; omega))
      (by intro slot member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl
          · exact ⟨root112, root112P⟩
          · exact ⟨root110, root110P⟩
          · exact ⟨root104, by rw [rootsP 104 (by decide)]; exact bound104⟩
          · exact ⟨root99, by rw [rootsP 99 (by decide)]; exact bound99⟩) heldP
  have last17 : Calling.Prefix callee callers (finishCode 56) ((finishActions.drop 39).take 17) wi ai final after :=
    Calling.Prefix.append (suffix := finishCode 56) (rest := (finishActions.drop 48).take 8) packing cleanup
  have same : ∀ slot, slot ∉ [0, 99, 104, 110, 111, 112] → (∀ value, ai.state slot ≠ .shared value) → after.state slot = ai.state slot := by
    intro slot outside unshared
    apply last17.unshared_local_same mi.native.valid mi.native.callersValid mi.native.wellFormed unshared (by decide +kernel)
    have different : slot ≠ 0 ∧ slot ≠ 99 ∧ slot ≠ 104 ∧ slot ≠ 110 ∧ slot ≠ 111 ∧ slot ≠ 112 := by simpa using outside
    simp [finishActions, SourceEval.LocalPreservation.action, SourceEval.LocalPreservation.expression, SourceEval.LocalPreservation.operands,
      SourceEval.LocalPreservation.operand, splitPlace, different.1, different.2.1, different.2.2.1, different.2.2.2.1, different.2.2.2.2.1, different.2.2.2.2.2]
  have preserved : ∀ slot, slot ∉ [0, 99, 104, 110, 111, 112] → ∀ ty, SlotTyped (ai.state slot) ty → Borrow.Closed ty → after.state slot = ai.state slot := by
    intro slot outside ty typed closed
    apply same slot outside
    intro value eq; rw [eq] at typed; cases typed; cases closed
  have finalScope : FinishPackedScope lh lt rh rt heads tails left right table total after := by
    refine ⟨(same 13 (by decide) (by rw [insertionScope.tuple]; intro value eq; cases eq)).trans insertionScope.tuple,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, outputAfter, ?_, ?_⟩
    · intro slot member
      have outside : slot ∉ [0, 99, 104, 110, 111, 112] := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; omega
      exact (preserved slot outside .u32 (by rw [insertionScope.endedViews slot member]; exact .empty _) .u32).trans (insertionScope.endedViews slot member)
    · exact (preserved 37 (by decide) (.adt .embedding) (by rw [insertionScope.headHole]; exact resultWordHole_typed _) (.adt .embedding)).trans insertionScope.headHole
    · exact (preserved 47 (by decide) (.adt .embedding) (by rw [insertionScope.tailHole]; exact resultWordHole_typed _) (.adt .embedding)).trans insertionScope.tailHole
    · exact (preserved 58 (by decide) .u32 (by rw [insertionScope.totalValue]; exact .number total.hmax) .u32).trans insertionScope.totalValue
    · exact (preserved 71 (by decide) (.adt .word) (by rw [insertionScope.leftWord]; exact ofValue_typed (word_typed _)) (.adt .word)).trans insertionScope.leftWord
    · exact (preserved 74 (by decide) (.adt .optional) (by rw [insertionScope.leftHole]; exact headPayloadHole_typed) (.adt .optional)).trans insertionScope.leftHole
    · exact (preserved 85 (by decide) (.adt .word) (by rw [insertionScope.rightWord]; exact ofValue_typed (word_typed _)) (.adt .word)).trans insertionScope.rightWord
    · exact (preserved 88 (by decide) (.adt .optional) (by rw [insertionScope.rightHole]; exact headPayloadHole_typed) (.adt .optional)).trans insertionScope.rightHole
    · exact (preserved 42 (by decide) .u32 (by rw [insertionScope.headTableEmpty]; exact .empty _) .u32).trans insertionScope.headTableEmpty
    · exact (preserved 75 (by decide) .u32 (by rw [insertionScope.leftTableEmpty]; exact .empty _) .u32).trans insertionScope.leftTableEmpty
    · intro slot member
      have alternatives : slot ∈ [64, 81, 89, 95, 100, 101, 102, 103, 105, 106, 107, 108, 109] ∨ slot ∈ [99, 104, 110, 111, 112] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; omega
      rcases alternatives with old | moved
      · have outside : slot ∉ [0, 99, 104, 110, 111, 112] := by simp only [List.mem_cons, List.not_mem_nil, or_false] at old ⊢; omega
        exact (preserved slot outside .u32 (by rw [insertionScope.moved slot old]; exact .empty _) .u32).trans (insertionScope.moved slot old)
      · by_cases eleven : slot = 111
        · subst slot
          exact sameAfter 111 (by decide) (by rw [emptyP 111 (by decide)]; intro value eq; cases eq) |>.trans (emptyP 111 (by decide))
        · exact (retiredAfter slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at moved ⊢; omega)).1
    · intro slot member
      have alternatives : slot ∈ [65, 70, 86, 87, 90, 91, 92, 93, 94, 96, 100, 101, 102, 103, 105, 106, 107, 108, 109] ∨ slot ∈ [99, 104, 110, 111, 112] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; omega
      rcases alternatives with old | moved
      · have outside : slot ∉ [112, 110, 104, 99] := by simp only [List.mem_cons, List.not_mem_nil, or_false] at old ⊢; omega
        have outsideP : slot ∉ [110, 111, 112] := by simp only [List.mem_cons, List.not_mem_nil, or_false] at old ⊢; omega
        rw [rootsAfter slot outside, rootsP slot outsideP]; exact insertionScope.retired slot old
      · by_cases eleven : slot = 111
        · subst slot; rw [rootsAfter 111 (by decide)]; exact dead111P
        · exact (retiredAfter slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at moved ⊢; omega)).2
  refine ⟨minFuel, minBudget, wi, ai, wa, aa, wp, ap, final, after, machine, finalScope, freshAfter, heldAfter,
    countAfter.trans (countP.trans countI), frameAfter.trans (frameP.trans frameI), ?_, ?_, ?_⟩
  · intro slot outside
    have oi : slot ∉ [99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; omega
    have op : slot ∉ [110, 111, 112] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; omega
    have oc : slot ∉ [112, 110, 104, 99] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; omega
    rw [rootsAfter slot oc, rootsP slot op, rootsI slot oi]
  · intro slot binding other0 other95 root raw read
    have oi : slot ∉ [99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109] := by
      intro member; rw [unbound slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; omega)] at root; cases root
    rw [memoryAfter]
    exact memoryP slot binding other0 (by rw [rootsI slot oi]; exact root) raw (memoryI slot binding other95 root raw read)
  · intro fuel budget hf hb
    have inserted := (stableI fuel budget hf hb).2.2.2.2.2
    have first := args.noncall_callee (Recursive.original budget fuel) (by decide +kernel)
    have assigned := assign0.noncall_callee (Recursive.original budget fuel) (by decide +kernel)
    have retired := cleanup.noncall_callee (Recursive.original budget fuel) (by decide +kernel)
    exact ⟨inserted, first, assigned, retired, Calling.Prefix.append (suffix := finishCode 56) (rest := (finishActions.drop 39).take 17)
      inserted (last17.noncall_callee (Recursive.original budget fuel) (by decide +kernel))⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
