module

public import SubtreeProofs.Rust.SourceTailFailureCleanup
public import SubtreeProofs.Rust.SourcePairTailScopeEntry

/-! Select tail failure, pack its actual updated table, drop the held head
witness, execute both cleanup joins and construct parameter cleanup/return. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem tail_failure_continuation_complete {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees)
    {lh lt rh rt : BalancedWord} {heads : CommonEmbedding} {table : MemoTable}
    (scope : PairTailScope initial lh lt rh rt heads none table world active)
    (present : rootPresence active.roots = fun slot => pairTailLiveRoots.contains slot)
    (count : 113 ≤ active.count) (headsFresh : LocalOwnersAbove before.memory.length world active 37) :
    ∃ branchWorld branchActive branchCost headWorld headActive headCost final after cell returnCost,
      Calling.exec callee callers tailCases world active = some (.next branchWorld branchActive, branchCost) ∧
      Calling.exec callee callers cleanupInputs branchWorld branchActive = some (.next headWorld headActive, headCost) ∧
      Calling.exec callee callers returnResult headWorld headActive = some (.returned final after (cell, encodeOutput none table), returnCost) ∧
      (∀ slot, after.state slot = .empty) ∧ after.RootsSeparate callers ∧
      (∀ slot binding, after.roots slot = some binding → before.memory.length ≤ binding.address) ∧
      Preserves before final previous.reads := by
  obtain ⟨root0, bound0, raw0⟩ := scope.returnRoot
  obtain ⟨packed, packetActive, packing, packedMachine, packedRoots, packedCount, _, output0, empty42⟩ :=
    failure_pack_complete h callee 42 49 50 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
      (rootPresence.absent present (by decide +kernel)) (rootPresence.absent present (by decide +kernel))
      scope.table bound0 raw0 scope.returnEmpty
  have presentP : rootPresence packetActive.roots = fun slot => pairTailLiveRoots.contains slot := by rw [packedRoots]; exact present
  have empty3 := packing.empty_untouched scope.tableEmpty (by decide +kernel)
  have hole31 := (packing.unshared_local_same_calls (by rw [scope.headHole]; intro value impossible; cases impossible)
    (by decide +kernel)).trans scope.headHole
  have empty32 := packing.empty_untouched scope.headTableEmpty (by decide +kernel)
  have none41 := (packing.closed_local_same_calls (by rw [scope.result]; exact ofValue_typed (option_typed none))
    (.adt .optional) (by decide +kernel)).trans scope.result
  have empty47 := packing.empty_untouched scope.payloadEmpty (by decide +kernel)
  have zero : ∀ slot ∈ tailFailureZeroSlots, (packetActive.state slot).dropWork.boxes = 0 := by
    intro slot member
    simp only [tailFailureZeroSlots, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact packedMachine.zero _ (by decide)
      | (rw [empty3]; simp only [Slot.dropWork])
      | (rw [hole31]; simp [headPayloadHole, Slot.dropWork, dropFields, DropWork.plus])
      | (rw [empty32]; simp only [Slot.dropWork])
      | (rw [none41]; simp [encodeOption, Slot.ofValue, ofFields, Slot.dropWork, dropFields])
      | (rw [empty42]; simp only [Slot.dropWork])
      | (rw [empty47]; simp only [Slot.dropWork])
  have freshP := packing.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by decide +kernel))
    h.native.valid h.native.callersValid h.native.wellFormed headsFresh
  obtain ⟨branchWorld, branchActive, headWorld, headActive, cleanupTail, cleanupHead, headMachine, presentHead, outputHead, empty3Head, _⟩ :=
    tail_failure_cleanup_complete packedMachine callee presentP (by rw [packedCount]; exact count) zero freshP empty3 output0
  obtain ⟨root0H, bound0H⟩ := rootPresence.bound presentHead (slot := 0) (by decide)
  obtain ⟨root1H, bound1H⟩ := rootPresence.bound presentHead (slot := 1) (by decide)
  obtain ⟨root2H, bound2H⟩ := rootPresence.bound presentHead (slot := 2) (by decide)
  obtain ⟨root3H, bound3H⟩ := rootPresence.bound presentHead (slot := 3) (by decide)
  have support : ∀ slot, slot ∉ [0, 1, 2, 3] → headActive.roots slot = none := by
    intro slot outside
    apply rootPresence.absent presentHead
    cases value : [0, 1, 2, 3].contains slot with
    | false => rfl
    | true => exact False.elim (outside (List.contains_iff_mem.mp value))
  obtain ⟨final, after, cell, returnCost, returned, empty, separate, fresh, kept⟩ :=
    original_return_complete headMachine callee bound0H bound1H bound2H bound3H support
      (by intro slot member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl <;> exact headMachine.zero _ (by decide)) empty3Head outputHead
  have inspection := Derived.scrutinee_complete h.native.valid h.native.callersValid _
    (tail_result_scrutinee_source scope.result) (by intros; trivial)
  obtain ⟨packCost, packRun⟩ := packing.exec (Calling.exec_done callee callers packed packetActive)
  have failureRun : Calling.exec callee callers tailsFailure world active = some (.next packed packetActive, packCost) := by
    rw [tailsFailure_actions]; exact packRun
  obtain ⟨cleanupCost, tailRun⟩ := cleanupTail.exec (Calling.exec_done callee callers branchWorld branchActive)
  have cleanupRun : Calling.exec callee callers cleanupHeads packed packetActive = some (.next branchWorld branchActive, cleanupCost) := by
    rw [cleanupHeads_actions]; exact tailRun
  have branchRun : Calling.exec callee callers tailCases world active = some (.next branchWorld branchActive,
      ((Cost.local (1 + (Scrutinee.discriminant (.local 41)).weight)).plus packCost).plus cleanupCost) := by
    rw [tailCases, Calling.exec_switch, inspection]
    simp only [lookupKey, Control.selectSource, Control.selectIndex, ite_true, failureRun, bind, Option.bind]
    rw [cleanupRun]
  obtain ⟨headCost, headRun⟩ := cleanupHead.exec (Calling.exec_done callee callers headWorld headActive)
  have cleanupInputsRun : Calling.exec callee callers cleanupInputs branchWorld branchActive = some (.next headWorld headActive, headCost) := by
    rw [cleanupInputs_actions]; exact headRun
  exact ⟨branchWorld, branchActive, _, headWorld, headActive, headCost, final, after, cell, returnCost,
    branchRun, cleanupInputsRun, returned, empty, separate, fresh, kept⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
