module

public import SubtreeProofs.Rust.SourceRootOverflowContext
public import SubtreeProofs.Rust.SourceSubtotalOverflowContinuation

/-! Shared failure cleanup after result packing. Scalar total storage and all
outer joins execute before the guarded parameter return. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_failure_outer_return_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees)
    (present : rootPresence active.roots = fun slot => (pairTailLiveRoots ++ [51, 58]).contains slot) (count : 113 ≤ active.count)
    (older : PairOlderMasks active) (empty42 : active.state 42 = .empty)
    (zero58 : (active.state 58).dropWork.boxes = 0)
    (headsFresh : LocalOwnersAbove before.memory.length world active 37)
    (tailsFresh : LocalOwnersAbove before.memory.length world active 47)
    {table : MemoTable} (output0 : active.state 0 = Slot.ofValue (encodeOutput none table)) :
    ∃ scoreWorld scoreActive scoreCost tailWorld tailActive tailCost headWorld headActive headCost
      joinWorld joinActive joinCost final after cell returnCost,
      Calling.exec callee callers cleanupSubtotal world active = some (.next scoreWorld scoreActive, scoreCost) ∧
      Calling.exec callee callers cleanupTails scoreWorld scoreActive = some (.next tailWorld tailActive, tailCost) ∧
      Calling.exec callee callers cleanupHeads tailWorld tailActive = some (.next headWorld headActive, headCost) ∧
      Calling.exec callee callers cleanupInputs headWorld headActive = some (.next joinWorld joinActive, joinCost) ∧
      Calling.exec callee callers returnResult joinWorld joinActive = some (.returned final after (cell, encodeOutput none table), returnCost) ∧
      (∀ slot, after.state slot = .empty) ∧ after.RootsSeparate callers ∧
      (∀ slot binding, after.roots slot = some binding → before.memory.length ≤ binding.address) ∧
      Preserves before final previous.reads := by
  have ready : retirementReady (rootPresence active.roots) rootCleanupActions = true := by
    rw [present]; decide +kernel
  obtain ⟨scoreWorld, scoreActive, cleanupSubtotal, scoreMachine, _, scoreCount, _⟩ :=
    (RetirementPlan.of_presence ready).complete_original callee .done h rfl (by
      intro slot member
      have selected : slot = 58 := by simpa [rootCleanupActions] using member
      subst slot
      exact zero58)
  have scorePresence : rootPresence scoreActive.roots = fun slot => (pairTailLiveRoots ++ [51]).contains slot := by
    rw [cleanupSubtotal.root_presence, present, rootPresence_fold_contains]
    have same : (rootCleanupActions.foldl rootSlotsStep (pairTailLiveRoots ++ [51, 58])).Perm (pairTailLiveRoots ++ [51]) := by decide +kernel
    funext slot
    exact Bool.eq_iff_iff.mpr (by simpa only [List.contains_iff_mem] using same.mem_iff)
  have masksS := older.through_prefix cleanupSubtotal (by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
  have empty42S := cleanupSubtotal.empty_untouched empty42 (by decide +kernel)
  have outputS := (cleanupSubtotal.closed_local_same_calls
    (by rw [output0]; exact ofValue_typed (encodeOutput_typed none table))
    (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (by decide +kernel)).trans output0
  have zero : ∀ slot ∈ tailFailureZeroSlots, slot ≠ 47 → (scoreActive.state slot).dropWork.boxes = 0 := by
    intro slot member different
    simp only [tailFailureZeroSlots, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact scoreMachine.zero _ (by decide)
      | (rw [masksS.tableEmpty]; simp only [Slot.dropWork])
      | (rw [masksS.headHole]; simp [Slot.dropWork, dropFields, DropWork.plus])
      | (rw [masksS.headTableEmpty]; simp only [Slot.dropWork])
      | (rw [masksS.tailHole]; simp [Slot.dropWork, dropFields, DropWork.plus])
      | (rw [empty42S]; simp only [Slot.dropWork])
      | exact False.elim (different rfl)
  have headsS := cleanupSubtotal.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by decide +kernel))
    h.native.valid h.native.callersValid h.native.wellFormed headsFresh
  have tailsS := cleanupSubtotal.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by decide +kernel))
    h.native.valid h.native.callersValid h.native.wellFormed tailsFresh
  obtain ⟨tailWorld, tailActive, headWorld, headActive, joinWorld, joinActive, cleanupTail, cleanupHead, cleanupInput,
    joinMachine, joinPresence, joinOutput, joinEmpty3, _⟩ :=
    subtotal_overflow_cleanup_complete scoreMachine callee scorePresence (by omega) zero masksS.subtotalZero
      headsS tailsS masksS.tableEmpty outputS
  obtain ⟨root0, bound0⟩ := rootPresence.bound joinPresence (slot := 0) (by decide)
  obtain ⟨root1, bound1⟩ := rootPresence.bound joinPresence (slot := 1) (by decide)
  obtain ⟨root2, bound2⟩ := rootPresence.bound joinPresence (slot := 2) (by decide)
  obtain ⟨root3, bound3⟩ := rootPresence.bound joinPresence (slot := 3) (by decide)
  have support : ∀ slot, slot ∉ [0, 1, 2, 3] → joinActive.roots slot = none := by
    intro slot outside
    apply rootPresence.absent joinPresence
    cases value : [0, 1, 2, 3].contains slot with
    | false => rfl
    | true => exact False.elim (outside (List.contains_iff_mem.mp value))
  obtain ⟨final, after, cell, returnCost, returned, empty, separate, fresh, kept⟩ :=
    original_return_complete joinMachine callee bound0 bound1 bound2 bound3 support
      (by intro slot member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl <;> exact joinMachine.zero _ (by decide)) joinEmpty3 joinOutput
  obtain ⟨subtotalCost, subtotalRun⟩ := cleanupSubtotal.exec (Calling.exec_done callee callers scoreWorld scoreActive)
  have subtotalWhole : Calling.exec callee callers Evaluator.cleanupSubtotal world active = some (.next scoreWorld scoreActive, subtotalCost) := by
    rw [cleanupSubtotal_actions]; exact subtotalRun
  obtain ⟨tailCost, tailRun⟩ := cleanupTail.exec (Calling.exec_done callee callers tailWorld tailActive)
  have cleanupTailsRun : Calling.exec callee callers cleanupTails scoreWorld scoreActive = some (.next tailWorld tailActive, tailCost) := by
    rw [cleanupTails_actions]; exact tailRun
  obtain ⟨headCost, headRun⟩ := cleanupHead.exec (Calling.exec_done callee callers headWorld headActive)
  have cleanupHeadsRun : Calling.exec callee callers cleanupHeads tailWorld tailActive = some (.next headWorld headActive, headCost) := by
    rw [cleanupHeads_actions]; exact headRun
  obtain ⟨joinCost, joinRun⟩ := cleanupInput.exec (Calling.exec_done callee callers joinWorld joinActive)
  have cleanupInputsRun : Calling.exec callee callers cleanupInputs headWorld headActive = some (.next joinWorld joinActive, joinCost) := by
    rw [cleanupInputs_actions]; exact joinRun
  exact ⟨scoreWorld, scoreActive, subtotalCost, tailWorld, tailActive, tailCost, headWorld, headActive, headCost,
    joinWorld, joinActive, joinCost, final, after, cell, returnCost,
    subtotalWhole, cleanupTailsRun, cleanupHeadsRun, cleanupInputsRun, returned, empty, separate, fresh, kept⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
