module

public import SubtreeProofs.Rust.SourceSubtotalOverflowCleanup
public import SubtreeProofs.Rust.SourceTailFailureContinuation

/-! Select the subtotal overflow arm, retire both held witnesses through their
owner bounds, and execute the real cleanup joins and parameter return. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem subtotal_overflow_continuation_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) {heads tails : CommonEmbedding} {table : MemoTable}
    (scope : ScoreSumScope heads tails table world active) (storage : EmptyRootStorage world active 0)
    (present : rootPresence active.roots = fun slot => pairScoreLiveRoots.contains slot) (count : 113 ≤ active.count)
    (hole31 : active.state 31 = headPayloadHole) (empty32 : active.state 32 = .empty)
    (hole41 : active.state 41 = .node .optional 1 [.empty]) (empty3 : active.state 3 = .empty)
    (headsFresh : LocalOwnersAbove before.memory.length world active 37)
    (tailsFresh : LocalOwnersAbove before.memory.length world active 47)
    (overflow : checkedAdd32 heads.edges.val tails.edges.val = none)
    (inspection : Derived.scrutinee world active callers (.discriminant (.local 52)) =
      some (numberKey (checkedAdd32 heads.edges.val tails.edges.val), active)) :
    ∃ tailWorld tailActive tailCost headWorld headActive headCost joinWorld joinActive joinCost final after cell returnCost,
      Calling.exec callee callers scoreCases world active = some (.next tailWorld tailActive, tailCost) ∧
      Calling.exec callee callers cleanupHeads tailWorld tailActive = some (.next headWorld headActive, headCost) ∧
      Calling.exec callee callers cleanupInputs headWorld headActive = some (.next joinWorld joinActive, joinCost) ∧
      Calling.exec callee callers returnResult joinWorld joinActive = some (.returned final after (cell, encodeOutput none table), returnCost) ∧
      (∀ slot, after.state slot = .empty) ∧ after.RootsSeparate callers ∧
      (∀ slot binding, after.roots slot = some binding → before.memory.length ≤ binding.address) ∧
      Preserves before final previous.reads := by
  obtain ⟨packed, packetActive, packing, packedMachine, packedPresence, output0, empty42, packedCount⟩ :=
    subtotal_overflow_pack_complete h callee scope storage present count
  have empty3P := packing.empty_untouched empty3 (by decide +kernel)
  have hole31P := (packing.unshared_local_same_calls (by rw [hole31]; intro value impossible; cases impossible)
    (by decide +kernel)).trans hole31
  have empty32P := packing.empty_untouched empty32 (by decide +kernel)
  have hole41P := packing.optional_hole_untouched hole41 (by decide +kernel)
  have empty51P := packing.empty_untouched scope.subtotalEmpty (by decide +kernel)
  have zero : ∀ slot ∈ tailFailureZeroSlots, slot ≠ 47 → (packetActive.state slot).dropWork.boxes = 0 := by
    intro slot member different
    simp only [tailFailureZeroSlots, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact packedMachine.zero _ (by decide)
      | (rw [empty3P]; simp only [Slot.dropWork])
      | (rw [hole31P]; simp [headPayloadHole, Slot.dropWork, dropFields, DropWork.plus])
      | (rw [empty32P]; simp only [Slot.dropWork])
      | (rw [hole41P]; simp [Slot.dropWork, dropFields, DropWork.plus])
      | (rw [empty42]; simp only [Slot.dropWork])
      | exact False.elim (different rfl)
  have headsP := packing.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by decide +kernel))
    h.native.valid h.native.callersValid h.native.wellFormed headsFresh
  have tailsP := packing.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by decide +kernel))
    h.native.valid h.native.callersValid h.native.wellFormed tailsFresh
  obtain ⟨tailWorld, tailActive, headWorld, headActive, joinWorld, joinActive, cleanupTail, cleanupHead, cleanupInput,
    joinMachine, joinPresence, joinOutput, joinEmpty3, _⟩ :=
    subtotal_overflow_cleanup_complete packedMachine callee packedPresence (by omega) zero
      (by rw [empty51P]; simp only [Slot.dropWork]) headsP tailsP empty3P output0
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
  obtain ⟨packCost, packRun⟩ := packing.exec (Calling.exec_done callee callers packed packetActive)
  have overflowRun : Calling.exec callee callers subtotalOverflow world active = some (.next packed packetActive, packCost) := by
    rw [subtotalOverflow_actions]; exact packRun
  obtain ⟨cleanupCost, tailRun⟩ := cleanupTail.exec (Calling.exec_done callee callers tailWorld tailActive)
  have cleanupRun : Calling.exec callee callers cleanupTails packed packetActive = some (.next tailWorld tailActive, cleanupCost) := by
    rw [cleanupTails_actions]; exact tailRun
  have scoreRun : Calling.exec callee callers scoreCases world active = some (.next tailWorld tailActive,
      ((Cost.local (1 + (Scrutinee.discriminant (.local 52)).weight)).plus packCost).plus cleanupCost) := by
    rw [scoreCases, Calling.exec_switch, inspection, overflow]
    simp only [numberKey, Control.selectSource, Control.selectIndex, ite_true, overflowRun, bind, Option.bind]
    rw [cleanupRun]
  obtain ⟨headCost, headRun⟩ := cleanupHead.exec (Calling.exec_done callee callers headWorld headActive)
  have cleanupHeadsRun : Calling.exec callee callers cleanupHeads tailWorld tailActive = some (.next headWorld headActive, headCost) := by
    rw [cleanupHeads_actions]; exact headRun
  obtain ⟨joinCost, joinRun⟩ := cleanupInput.exec (Calling.exec_done callee callers joinWorld joinActive)
  have cleanupInputsRun : Calling.exec callee callers cleanupInputs headWorld headActive = some (.next joinWorld joinActive, joinCost) := by
    rw [cleanupInputs_actions]; exact joinRun
  exact ⟨tailWorld, tailActive, _, headWorld, headActive, headCost, joinWorld, joinActive, joinCost,
    final, after, cell, returnCost, scoreRun, cleanupHeadsRun, cleanupInputsRun, returned, empty, separate, fresh, kept⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
