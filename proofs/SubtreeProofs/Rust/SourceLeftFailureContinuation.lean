module

public import SubtreeProofs.Rust.SourceLeftFailureCleanup

/-! Construct the left None arm, updated-table packing, both owned drops and
all five cleanup joins through the guarded return. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem left_failure_continuation_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) {lh lt rh rt : BalancedWord} {heads tails : CommonEmbedding}
    {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : PairLeftScope lh lt rh rt heads tails total none table world active)
    (storage : EmptyRootStorage world active 0) (older : PairOlderMasks active)
    (present : rootPresence active.roots = fun slot => pairLeftLiveRoots.contains slot) (count : 113 ≤ active.count)
    (held : ∀ slot ∈ [64, 71], LocalOwnersAbove before.memory.length world active slot) :
    ∃ leftWorld leftActive leftCost scoreWorld scoreActive scoreCost tailWorld tailActive tailCost
      headWorld headActive headCost joinWorld joinActive joinCost final after cell returnCost,
      Calling.exec callee callers matchedCases world active = some (.next leftWorld leftActive, leftCost) ∧
      Calling.exec callee callers cleanupSubtotal leftWorld leftActive = some (.next scoreWorld scoreActive, scoreCost) ∧
      Calling.exec callee callers cleanupTails scoreWorld scoreActive = some (.next tailWorld tailActive, tailCost) ∧
      Calling.exec callee callers cleanupHeads tailWorld tailActive = some (.next headWorld headActive, headCost) ∧
      Calling.exec callee callers cleanupInputs headWorld headActive = some (.next joinWorld joinActive, joinCost) ∧
      Calling.exec callee callers returnResult joinWorld joinActive = some (.returned final after (cell, encodeOutput none table), returnCost) ∧
      (∀ slot, after.state slot = .empty) ∧ after.RootsSeparate callers ∧
      (∀ slot binding, after.roots slot = some binding → before.memory.length ≤ binding.address) ∧
      Preserves before final previous.reads := by
  obtain ⟨root0, bound0, raw0⟩ := storage.root
  obtain ⟨packed, packetActive, packing, packedMachine, packedRoots, packedCount, _, output0, empty75⟩ :=
    failure_pack_complete h callee 75 83 84 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
      (rootPresence.absent present (by decide +kernel)) (rootPresence.absent present (by decide +kernel))
      scope.tableValue bound0 raw0 storage.empty
  have presentP : rootPresence packetActive.roots = fun slot => pairLeftLiveRoots.contains slot := by rw [packedRoots]; exact present
  have none74 := (packing.closed_local_same_calls (by rw [scope.resultValue]; exact ofValue_typed (option_typed none))
    (.adt .optional) (by decide +kernel)).trans scope.resultValue
  have empty81 := packing.empty_untouched scope.payloadEmpty (by decide +kernel)
  have zero : ∀ slot ∈ [74, 75, 81], (packetActive.state slot).dropWork.boxes = 0 := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · rw [none74]; simp [encodeOption, Slot.ofValue, ofFields, Slot.dropWork, dropFields]
    · rw [empty75]; simp only [Slot.dropWork]
    · rw [empty81]; simp only [Slot.dropWork]
  have heldP : ∀ slot ∈ [64, 71], LocalOwnersAbove before.memory.length packed packetActive slot := by
    intro slot member
    have kept : OwnerTransfer slot (failurePackActions 75 83 84) slot := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact OwnerTransfer.kept (by decide +kernel) (by decide +kernel)
    exact packing.owner_transfer kept h.native.valid h.native.callersValid h.native.wellFormed (held slot member)
  obtain ⟨leftWorld, leftActive, cleanup, leftMachine, leftPresence, leftOutput, leftCount⟩ :=
    left_failure_cleanup_complete packedMachine callee presentP (by omega) zero heldP output0
  have masksP := older.through_prefix packing (by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
  have masksL := masksP.through_prefix cleanup (by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
  have headZero : (leftActive.state 37).dropWork.boxes = 0 := by
    rw [cleanup.boxes_same_calls (by decide +kernel), packing.boxes_same_calls (by decide +kernel), scope.matched.headHole]
    simp [resultWordHole, Slot.dropWork, dropFields, DropWork.plus]
  have tailZero : (leftActive.state 47).dropWork.boxes = 0 := by
    rw [cleanup.boxes_same_calls (by decide +kernel), packing.boxes_same_calls (by decide +kernel), scope.matched.tailHole]
    simp [resultWordHole, Slot.dropWork, dropFields, DropWork.plus]
  have zero58 : (leftActive.state 58).dropWork.boxes = 0 := by
    rw [cleanup.boxes_same_calls (by decide +kernel), packing.boxes_same_calls (by decide +kernel), scope.matched.totalValue]
    simp only [Slot.dropWork]
  obtain ⟨scoreWorld, scoreActive, scoreCost, tailWorld, tailActive, tailCost, headWorld, headActive, headCost,
    joinWorld, joinActive, joinCost, final, after, cell, returnCost, subtotalRun, tailsRun, headsRun, inputsRun,
    returned, empty, separate, fresh, kept⟩ :=
    pair_failure_outer_return_complete leftMachine callee leftPresence (by omega) masksL
      (cleanup.empty_untouched (packing.empty_untouched scope.oldTableEmpty (by decide +kernel)) (by decide +kernel))
      zero58 (.of_zero headZero) (.of_zero tailZero) leftOutput
  obtain ⟨packCost, packRun⟩ := packing.exec (Calling.exec_done callee callers packed packetActive)
  have failureRun : Calling.exec callee callers leftFailure world active = some (.next packed packetActive, packCost) := by
    rw [leftFailure_actions]; exact packRun
  obtain ⟨cleanupCost, cleanupRun⟩ := cleanup.exec (Calling.exec_done callee callers leftWorld leftActive)
  have cleanupWhole : Calling.exec callee callers cleanupLeft packed packetActive = some (.next leftWorld leftActive, cleanupCost) := by
    rw [cleanupLeft_actions]; exact cleanupRun
  have inspection := Derived.scrutinee_complete h.native.valid h.native.callersValid _
    (left_result_scrutinee_source scope.resultValue) (by intros; trivial)
  have leftRun : Calling.exec callee callers matchedCases world active = some (.next leftWorld leftActive,
      ((Cost.local (1 + (Scrutinee.discriminant (.local 74)).weight)).plus packCost).plus cleanupCost) := by
    rw [matchedCases, Calling.exec_switch, inspection]
    simp only [lookupKey, Control.selectSource, Control.selectIndex, ite_true, failureRun, bind, Option.bind]
    rw [cleanupWhole]
  exact ⟨leftWorld, leftActive, _, scoreWorld, scoreActive, scoreCost, tailWorld, tailActive, tailCost,
    headWorld, headActive, headCost, joinWorld, joinActive, joinCost, final, after, cell, returnCost,
    leftRun, subtotalRun, tailsRun, headsRun, inputsRun, returned, empty, separate, fresh, kept⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
