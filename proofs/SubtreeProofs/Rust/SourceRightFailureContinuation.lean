module

public import SubtreeProofs.Rust.SourceRightFailureCleanup

/-! Select right None, execute its actual failure join, drop both owned
queries/left witness/candidate and follow all outer cleanup joins to return. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem right_failure_continuation_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) {lh lt rh rt : BalancedWord} {heads tails leftWitness : CommonEmbedding}
    {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : PairRightScope lh lt rh rt heads tails leftWitness total none table world active)
    (storage : EmptyRootStorage world active 0) (older : PairOlderMasks active)
    (present : rootPresence active.roots = fun slot => pairRightLiveRoots.contains slot) (count : 113 ≤ active.count)
    (held : ∀ slot ∈ [64, 71, 81, 85], LocalOwnersAbove before.memory.length world active slot) :
    ∃ rightWorld rightActive rightCost leftWorld leftActive leftCost scoreWorld scoreActive scoreCost tailWorld tailActive tailCost
      headWorld headActive headCost joinWorld joinActive joinCost final after cell returnCost,
      Calling.exec callee callers rightContractionCases world active = some (.next rightWorld rightActive, rightCost) ∧
      Calling.exec callee callers cleanupLeft rightWorld rightActive = some (.next leftWorld leftActive, leftCost) ∧
      Calling.exec callee callers cleanupSubtotal leftWorld leftActive = some (.next scoreWorld scoreActive, scoreCost) ∧
      Calling.exec callee callers cleanupTails scoreWorld scoreActive = some (.next tailWorld tailActive, tailCost) ∧
      Calling.exec callee callers cleanupHeads tailWorld tailActive = some (.next headWorld headActive, headCost) ∧
      Calling.exec callee callers cleanupInputs headWorld headActive = some (.next joinWorld joinActive, joinCost) ∧
      Calling.exec callee callers returnResult joinWorld joinActive = some (.returned final after (cell, encodeOutput none table), returnCost) ∧
      (∀ slot, after.state slot = .empty) ∧ after.RootsSeparate callers ∧
      (∀ slot binding, after.roots slot = some binding → before.memory.length ≤ binding.address) ∧
      Preserves before final previous.reads := by
  obtain ⟨root0, bound0, raw0⟩ := storage.root
  obtain ⟨packed, packetActive, packing, packedMachine, packedRoots, packedCount, _, output0, empty89⟩ :=
    failure_pack_complete_with_suffix h callee (rightFailureCleanupActions.foldr Control.Tree.step .done) 89 97 98
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by omega) (by omega)
      (rootPresence.absent present (by decide +kernel)) (rootPresence.absent present (by decide +kernel))
      scope.tableValue bound0 raw0 storage.empty
  have presentP : rootPresence packetActive.roots = fun slot => pairRightLiveRoots.contains slot := by rw [packedRoots]; exact present
  have none88 := (packing.closed_local_same_calls (by rw [scope.resultValue]; exact ofValue_typed (option_typed none))
    (.adt .optional) (by decide +kernel)).trans scope.resultValue
  have empty95 := packing.empty_untouched scope.payloadEmpty (by decide +kernel)
  have zero : ∀ slot ∈ [88, 89, 95], (packetActive.state slot).dropWork.boxes = 0 := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · rw [none88]; simp [encodeOption, Slot.ofValue, ofFields, Slot.dropWork, dropFields]
    · rw [empty89]; simp only [Slot.dropWork]
    · rw [empty95]; simp only [Slot.dropWork]
  have heldP : ∀ slot ∈ [64, 71, 81, 85], LocalOwnersAbove before.memory.length packed packetActive slot := by
    intro slot member
    have kept : OwnerTransfer slot (failurePackActions 89 97 98) slot := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> exact OwnerTransfer.kept (by decide +kernel) (by decide +kernel)
    exact packing.owner_transfer kept h.native.valid h.native.callersValid h.native.wellFormed (held slot member)
  obtain ⟨rightWorld, rightActive, rightCleanup, rightMachine, rightPresence, rightOutput, zero81, rightCount⟩ :=
    right_failure_cleanup_complete packedMachine callee presentP (by omega) zero
      (by intro slot member; exact heldP slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; omega)) output0
  have hole74 := (rightCleanup.optional_hole_untouched
    (packing.optional_hole_untouched scope.held.leftHole (by decide +kernel)) (by decide +kernel))
  have empty75 := rightCleanup.empty_untouched (packing.empty_untouched scope.oldTableEmpty (by decide +kernel)) (by decide +kernel)
  have leftZero : ∀ slot ∈ [74, 75, 81], (rightActive.state slot).dropWork.boxes = 0 := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · rw [hole74]; simp [Slot.dropWork, dropFields, DropWork.plus]
    · rw [empty75]; simp only [Slot.dropWork]
    · exact zero81
  have heldR : ∀ slot ∈ [64, 71], LocalOwnersAbove before.memory.length rightWorld rightActive slot := by
    intro slot member
    have kept : OwnerTransfer slot rightFailureCleanupActions slot := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact OwnerTransfer.kept (by decide +kernel) (by decide +kernel)
    exact rightCleanup.owner_transfer kept packedMachine.native.valid packedMachine.native.callersValid packedMachine.native.wellFormed
      (heldP slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; omega))
  obtain ⟨leftWorld, leftActive, cleanup, leftMachine, leftPresence, leftOutput, leftCount⟩ :=
    left_failure_cleanup_complete rightMachine callee rightPresence (by omega) leftZero heldR rightOutput
  have masksP := older.through_prefix packing (by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
  have masksR := masksP.through_prefix rightCleanup (by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
  have masksL := masksR.through_prefix cleanup (by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
  have headZero : (leftActive.state 37).dropWork.boxes = 0 := by
    rw [cleanup.boxes_same_calls (by decide +kernel), rightCleanup.boxes_same_calls (by decide +kernel), packing.boxes_same_calls (by decide +kernel), scope.held.matched.headHole]
    simp [resultWordHole, Slot.dropWork, dropFields, DropWork.plus]
  have tailZero : (leftActive.state 47).dropWork.boxes = 0 := by
    rw [cleanup.boxes_same_calls (by decide +kernel), rightCleanup.boxes_same_calls (by decide +kernel), packing.boxes_same_calls (by decide +kernel), scope.held.matched.tailHole]
    simp [resultWordHole, Slot.dropWork, dropFields, DropWork.plus]
  have zero58 : (leftActive.state 58).dropWork.boxes = 0 := by
    rw [cleanup.boxes_same_calls (by decide +kernel), rightCleanup.boxes_same_calls (by decide +kernel), packing.boxes_same_calls (by decide +kernel), scope.held.matched.totalValue]
    simp only [Slot.dropWork]
  obtain ⟨scoreWorld, scoreActive, scoreCost, tailWorld, tailActive, tailCost, headWorld, headActive, headCost,
    joinWorld, joinActive, joinCost, final, after, cell, returnCost, subtotalRun, tailsRun, headsRun, inputsRun,
    returned, empty, separate, fresh, kept⟩ :=
    pair_failure_outer_return_complete leftMachine callee leftPresence (by omega) masksL
      (cleanup.empty_untouched (rightCleanup.empty_untouched (packing.empty_untouched scope.held.oldTableEmpty (by decide +kernel)) (by decide +kernel)) (by decide +kernel))
      zero58 (.of_zero headZero) (.of_zero tailZero) leftOutput
  have whole : Calling.Prefix callee callers .done rightFailureActions world active rightWorld rightActive :=
    Calling.Prefix.append (suffix := .done) (rest := rightFailureCleanupActions) packing rightCleanup
  obtain ⟨failureCost, failureRun⟩ := whole.exec (Calling.exec_done callee callers rightWorld rightActive)
  have failureWhole : Calling.exec callee callers rightFailure world active = some (.next rightWorld rightActive, failureCost) := by
    rw [rightFailure_actions]; exact failureRun
  have inspection := Derived.scrutinee_complete h.native.valid h.native.callersValid _
    (right_result_scrutinee_source scope.resultValue) (by intros; trivial)
  have rightRun : Calling.exec callee callers rightContractionCases world active = some (.next rightWorld rightActive,
      ((Cost.local (1 + (Scrutinee.discriminant (.local 88)).weight)).plus {}).plus failureCost) := by
    rw [rightContractionCases, Calling.exec_switch, inspection]
    simp [lookupKey, Control.selectSource, Control.selectIndex, Calling.exec_done, failureWhole]
  obtain ⟨cleanupCost, cleanupRun⟩ := cleanup.exec (Calling.exec_done callee callers leftWorld leftActive)
  have cleanupWhole : Calling.exec callee callers cleanupLeft rightWorld rightActive = some (.next leftWorld leftActive, cleanupCost) := by
    rw [cleanupLeft_actions]; exact cleanupRun
  exact ⟨rightWorld, rightActive, _, leftWorld, leftActive, cleanupCost, scoreWorld, scoreActive, scoreCost,
    tailWorld, tailActive, tailCost, headWorld, headActive, headCost, joinWorld, joinActive, joinCost, final, after, cell, returnCost,
    rightRun, cleanupWhole, subtotalRun, tailsRun, headsRun, inputsRun, returned, empty, separate, fresh, kept⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
