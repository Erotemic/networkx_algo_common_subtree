module

public import SubtreeProofs.Rust.SourcePairChoices

/-! Successful right payload extraction and both real choices reach the actual
insertion continuation. Native query/table snapshots and both owned query
bounds survive while moved candidate and argument storage is recorded empty. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

structure FinishChoicesScope (lh lt rh rt : BalancedWord) (heads tails left right : CommonEmbedding)
    (table : MemoTable) (total : Aeneas.Std.U32) (active : Activation) : Prop where
  leftQuery : active.state 1 = .shared (encodeWord (.Pair lh lt))
  rightQuery : active.state 2 = .shared (encodeWord (.Pair rh rt))
  tuple : active.state 13 = queryTuple (.Pair lh lt) (.Pair rh rt)
  endedViews : ∀ slot ∈ [27, 28, 29, 30], active.state slot = .empty
  headHole : active.state 37 = resultWordHole heads.edges
  tailHole : active.state 47 = resultWordHole tails.edges
  totalValue : active.state 58 = .number total.val
  leftWord : active.state 71 = Slot.ofValue (encodeWord (OrderedSolver.appendWord lh lt))
  leftHole : active.state 74 = headPayloadHole
  rightWord : active.state 85 = Slot.ofValue (encodeWord (OrderedSolver.appendWord rh rt))
  rightHole : active.state 88 = headPayloadHole
  tableValue : active.state 89 = Slot.ofValue (encodeTable table)
  headTableEmpty : active.state 42 = .empty
  leftTableEmpty : active.state 75 = .empty
  selected : active.state 99 = Slot.ofValue (encodeResult (selectedWitness (matchedWitness heads tails total) left right))
  moved : ∀ slot ∈ [64, 81, 95, 100, 101, 102, 103], active.state slot = .empty
  retired : ∀ slot ∈ [65, 70, 86, 87, 90, 91, 92, 93, 94, 96, 100, 101, 102, 103], active.roots slot = none

theorem pair_finish_choices_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {lh lt rh rt : BalancedWord} {heads tails left right : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : PairRightScope lh lt rh rt heads tails left total (some right) table world active)
    (above : LocalOwnersAbove before.memory.length world active 88)
    (heldAbove : ∀ slot ∈ [64, 71, 81, 85], LocalOwnersAbove before.memory.length world active slot)
    (count : 104 ≤ active.count) (unbound : ∀ slot ∈ [96, 99, 100, 101, 102, 103], active.roots slot = none) :
    ∃ (payloadWorld : World) (payloadActive : Activation) (firstArgumentWorld : World) (firstArgumentActive : Activation) (firstCallWorld : World) (firstCallActive : Activation) (middle : World) (current : Activation) (secondArgumentWorld : World) (secondArgumentActive : Activation) (secondCallWorld : World) (secondCallActive : Activation) (final : World) (after : Activation),
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      FinishChoicesScope lh lt rh rt heads tails left right table total after ∧
      LocalOwnersAbove before.memory.length final after 99 ∧
      (∀ slot ∈ [71, 85], LocalOwnersAbove before.memory.length final after slot) ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [99, 100, 101, 102, 103] → after.roots slot = active.roots slot) ∧
      (∀ slot binding, slot ≠ 95 → active.roots slot = some binding → ∀ cell,
        world.memory[binding.address]? = some cell → final.memory[binding.address]? = some cell) ∧
      ∀ fuel budget, 0 < fuel →
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 6) (finishActions.take 6) world active payloadWorld payloadActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 15) ((finishActions.drop 6).take 9) payloadWorld payloadActive middle current ∧
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 21) ((finishActions.drop 15).take 6) middle current final after ∧
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 21) ((finishActions.drop 6).take 15) payloadWorld payloadActive final after ∧
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 21) (finishActions.take 21) world active final after ∧
        Derived.call (Recursive.original budget fuel) firstArgumentWorld (firstArgumentActive.forgetRefs (finishCode 12)) callers
          .chooseLonger [.move (.local 101), .move (.local 102)] 100 =
            some (firstCallWorld, firstCallActive, choiceCallCost 101 102 100 (matchedWitness heads tails total) left) ∧
        Derived.call (Recursive.original budget fuel) secondArgumentWorld (secondArgumentActive.forgetRefs (finishCode 17)) callers
          .chooseLonger [.move (.local 100), .move (.local 103)] 99 =
            some (secondCallWorld, secondCallActive, choiceCallCost 100 103 99 (OrderedSolver.selectResult (matchedWitness heads tails total) left) right) := by
  obtain ⟨wp, ap, payload, mp, payloadScope, rightFresh, heldFresh, rootsP, countP, frameP, memoryP⟩ :=
    pair_finish_payload_complete_provenance h (Helpers.callee 0 0) scope above heldAbove (by omega) (unbound 96 (by simp))
  obtain ⟨wa1, aa1, wc1, ac1, middle, current, wa2, aa2, wc2, ac2, final, after, machine, selected, moved, retired,
    countAfter, frameAfter, rootsAfter, selectedFresh, wordFresh, kept, queries, memoryAfter, stable⟩ :=
    pair_choices_complete mp (matchedWitness heads tails total) left right payloadScope.matched.candidate payloadScope.leftWitness payloadScope.rightWitness
      (heldFresh 64 (by simp)) (heldFresh 81 (by simp)) rightFresh
      (by intro slot member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl <;> exact heldFresh _ (by simp))
      (by rw [countP]; exact count) (by intro slot member; rw [rootsP]; exact unbound slot (List.mem_cons_of_mem 96 member))
  have preserved : ∀ slot, slot ∉ [64, 81, 95, 99, 100, 101, 102, 103] → ∀ ty,
      SlotTyped (ap.state slot) ty → Borrow.Closed ty → after.state slot = ap.state slot := by
    intro slot outside ty typed closed
    apply kept slot outside
    intro value eq
    rw [eq] at typed
    cases typed
    cases closed
  have finalScope : FinishChoicesScope lh lt rh rt heads tails left right table total after := by
    refine ⟨(queries 1 (by simp)).trans payloadScope.leftQuery, (queries 2 (by simp)).trans payloadScope.rightQuery,
      (kept 13 (by decide) (by rw [payloadScope.tuple]; intro value same; cases same)).trans payloadScope.tuple, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      selected, moved, ?_⟩
    · intro slot member
      have outside : slot ∉ [64, 81, 95, 99, 100, 101, 102, 103] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide
      exact (preserved slot outside .u32 (by rw [payloadScope.endedViews slot member]; exact .empty _) .u32).trans (payloadScope.endedViews slot member)
    · exact (preserved 37 (by decide) (.adt .embedding) (by rw [payloadScope.matched.headHole]; exact resultWordHole_typed heads.edges) (.adt .embedding)).trans payloadScope.matched.headHole
    · exact (preserved 47 (by decide) (.adt .embedding) (by rw [payloadScope.matched.tailHole]; exact resultWordHole_typed tails.edges) (.adt .embedding)).trans payloadScope.matched.tailHole
    · exact (preserved 58 (by decide) .u32 (by rw [payloadScope.matched.totalValue]; exact .number total.hmax) .u32).trans payloadScope.matched.totalValue
    · exact (preserved 71 (by decide) (.adt .word) (by rw [payloadScope.leftWord]; exact ofValue_typed (word_typed _)) (.adt .word)).trans payloadScope.leftWord
    · exact (preserved 74 (by decide) (.adt .optional) (by rw [payloadScope.leftHole]; exact headPayloadHole_typed) (.adt .optional)).trans payloadScope.leftHole
    · exact (preserved 85 (by decide) (.adt .word) (by rw [payloadScope.rightWord]; exact ofValue_typed (word_typed _)) (.adt .word)).trans payloadScope.rightWord
    · exact (preserved 88 (by decide) (.adt .optional) (by rw [payloadScope.rightHole]; exact headPayloadHole_typed) (.adt .optional)).trans payloadScope.rightHole
    · exact (preserved 89 (by decide) (.adt .table) (by rw [payloadScope.tableValue]; exact ofValue_typed (table_typed table)) (.adt .table)).trans payloadScope.tableValue
    · exact (preserved 42 (by decide) .u32 (by rw [payloadScope.headTableEmpty]; exact .empty _) .u32).trans payloadScope.headTableEmpty
    · exact (preserved 75 (by decide) .u32 (by rw [payloadScope.leftTableEmpty]; exact .empty _) .u32).trans payloadScope.leftTableEmpty
    · intro slot member
      have selected : slot = 65 ∨ slot = 70 ∨ slot ∈ [86, 87, 90, 91, 92, 93, 94, 96] ∨ slot ∈ [100, 101, 102, 103] := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] using member
      rcases selected with rfl | rfl | old | fresh
      · rw [rootsAfter 65 (by decide)]; exact payloadScope.matched.retired 65 (by simp)
      · rw [rootsAfter 70 (by decide)]; exact payloadScope.matched.retired 70 (by simp)
      · have outside : slot ∉ [99, 100, 101, 102, 103] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at old
          rcases old with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        rw [rootsAfter slot outside]
        exact payloadScope.retired slot old
      · exact retired slot fresh
  refine ⟨wp, ap, wa1, aa1, wc1, ac1, middle, current, wa2, aa2, wc2, ac2, final, after, machine, finalScope,
    selectedFresh, wordFresh, countAfter.trans countP, frameAfter.trans frameP, ?_, ?_, ?_⟩
  · intro slot outside; rw [rootsAfter slot outside, rootsP]
  · intro slot binding not95 root cell read
    have rootP : ap.roots slot = some binding := by rw [rootsP]; exact root
    exact memoryAfter slot binding rootP cell (memoryP slot binding not95 root cell read)
  · intro fuel budget positive
    obtain ⟨first9, second6, both, firstCall, secondCall⟩ := stable fuel budget positive
    have payloadRun := payload.noncall_callee (Recursive.original budget fuel) (by decide +kernel)
    exact ⟨payloadRun, first9, second6, both, Calling.Prefix.append (suffix := finishCode 21) (rest := (finishActions.drop 6).take 15) payloadRun both,
      firstCall, secondCall⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
