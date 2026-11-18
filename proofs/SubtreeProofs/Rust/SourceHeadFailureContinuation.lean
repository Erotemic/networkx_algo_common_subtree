module

public import SubtreeProofs.Rust.SourceHeadFailureCleanup

/-! Select actual head failure, pack its native updated table, retire every
head input temporary, and construct the outer parameter cleanup and return. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem queryTuple_materialize (left right : BalancedWord) :
    (queryTuple left right).materialize = some (.node .tuple 0 [.reference (encodeWord left), .reference (encodeWord right)]) := by
  simp [queryTuple, Slot.materialize, materializeFields]

theorem head_failure_continuation_complete {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [35, 34, 30, 29, 28, 27, 1, 2, 13] world active) (callee : Derived.Callees)
    {lh lt rh rt : BalancedWord} {table : MemoTable} (scope : PairHeadScope initial lh lt rh rt none table world active)
    (support : ∀ slot, slot ∉ [0, 1, 2, 3, 13] → initial.roots slot = none)
    (count : 41 ≤ active.count) {root3 : Binding} (bound3 : active.roots 3 = some root3) :
    ∃ branchWorld branchActive branchCost final after cell returnCost,
      Calling.exec callee callers headCases world active = some (.next branchWorld branchActive, branchCost) ∧
      Calling.exec callee callers returnResult branchWorld branchActive =
        some (.returned final after (cell, encodeOutput none table), returnCost) ∧
      (∀ slot, after.state slot = .empty) ∧ after.RootsSeparate callers ∧
      (∀ slot binding, after.roots slot = some binding → before.memory.length ≤ binding.address) ∧
      Preserves before final previous.reads := by
  have unbound39 : active.roots 39 = none := by rw [scope.otherRoots 39 (by decide)]; exact support 39 (by decide)
  have unbound40 : active.roots 40 = none := by rw [scope.otherRoots 40 (by decide)]; exact support 40 (by decide)
  obtain ⟨root0, bound0, raw0⟩ := scope.returnRoot
  obtain ⟨packed, packetActive, packing, packedMachine, packedRoots, packedCount, packedFrame, output0, empty32⟩ :=
    failure_pack_complete h callee 32 39 40 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
      unbound39 unbound40 scope.table bound0 raw0 scope.returnEmpty
  have none31 : packetActive.state 31 = Slot.ofValue (encodeOption none) :=
    (packing.closed_local_same (index := 31) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.result]; exact ofValue_typed (option_typed none)) (.adt .optional) (by decide +kernel) (by decide +kernel)).trans scope.result
  have empty37 : packetActive.state 37 = .empty :=
    (packing.closed_local_same (index := 37) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.payloadEmpty]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans scope.payloadEmpty
  have empty3 : packetActive.state 3 = .empty :=
    (packing.closed_local_same (index := 3) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.tableEmpty]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans scope.tableEmpty
  obtain ⟨root13, bound13⟩ := Activation.root_of_materialize h.native.valid (by rw [scope.tuple]; exact queryTuple_materialize _ _)
  have cleanupBound : ∀ slot ∈ [13, 27, 28, 29, 30, 31, 32, 37], ∃ binding, packetActive.roots slot = some binding := by
    intro slot member
    rw [packedRoots]
    rcases List.mem_cons.mp member with rfl | rest
    · exact ⟨root13, bound13⟩
    · exact scope.live slot rest
  obtain ⟨branchWorld, branchActive, cleanup, branchMachine, cleanupRoots, cleanupCount, outputAfter, empty3After⟩ :=
    head_failure_cleanup_complete packedMachine callee cleanupBound none31 empty32 empty37 empty3 output0
  have observed := Derived.scrutinee_complete h.native.valid h.native.callersValid _ (head_result_scrutinee_source scope.result) (by intros; trivial)
  obtain ⟨packCost, packRun⟩ := packing.exec (Calling.exec_done callee callers packed packetActive)
  have failureRun : Calling.exec callee callers headsFailure world active = some (.next packed packetActive, packCost) := by
    rw [headsFailure_actions]; exact packRun
  obtain ⟨cleanCost, cleanRun⟩ := cleanup.exec (Calling.exec_done callee callers branchWorld branchActive)
  have inputCleanup : Calling.exec callee callers cleanupInputs packed packetActive = some (.next branchWorld branchActive, cleanCost) := by
    rw [cleanupInputs_actions]; exact cleanRun
  have branchRun : Calling.exec callee callers headCases world active = some (.next branchWorld branchActive,
      ((Cost.local (1 + (Scrutinee.discriminant (.local 31)).weight)).plus packCost).plus cleanCost) := by
    rw [headCases, Calling.exec_switch, observed]
    simp only [lookupKey, Control.selectSource, Control.selectIndex, ite_true, failureRun, bind, Option.bind]
    rw [inputCleanup]
  obtain ⟨root1, bound1⟩ := Activation.root_of_materialize h.native.valid (value := .reference (encodeWord (.Pair lh lt))) (by rw [scope.left]; simp only [Slot.materialize])
  obtain ⟨root2, bound2⟩ := Activation.root_of_materialize h.native.valid (value := .reference (encodeWord (.Pair rh rt))) (by rw [scope.right]; simp only [Slot.materialize])
  have supportPacked : ∀ slot, slot ∉ [0, 1, 2, 3, 13, 27, 28, 29, 30, 31, 32, 37] → packetActive.roots slot = none := by
    intro slot outside
    rw [packedRoots]
    by_cases retired : slot ∈ [33, 34, 35, 36]
    · exact scope.retired slot retired
    · rw [scope.otherRoots slot (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside retired ⊢; tauto)]
      exact support slot (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto)
  have supportAfter : ∀ slot, slot ∉ [0, 1, 2, 3] → branchActive.roots slot = none := by
    intro slot outside
    rw [cleanupRoots]
    by_cases i13 : slot = 13
    · subst slot; simp [headCleanupRoots, Roots.set]
    by_cases i27 : slot = 27
    · subst slot; simp [headCleanupRoots, Roots.set]
    by_cases i28 : slot = 28
    · subst slot; simp [headCleanupRoots, Roots.set]
    by_cases i29 : slot = 29
    · subst slot; simp [headCleanupRoots, Roots.set]
    by_cases i30 : slot = 30
    · subst slot; simp [headCleanupRoots, Roots.set]
    by_cases i31 : slot = 31
    · subst slot; simp [headCleanupRoots, Roots.set]
    by_cases i32 : slot = 32
    · subst slot; simp [headCleanupRoots, Roots.set]
    by_cases i37 : slot = 37
    · subst slot; simp [headCleanupRoots, Roots.set]
    simp only [headCleanupRoots, Roots.set, i13, i27, i28, i29, i30, i31, i32, i37, ite_false]
    exact supportPacked slot (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto)
  obtain ⟨final, after, cell, returnCost, returned, empty, separate, fresh, kept⟩ :=
    original_return_complete branchMachine callee
      (by simpa [cleanupRoots, headCleanupRoots, packedRoots, Roots.set] using bound0)
      (by simpa [cleanupRoots, headCleanupRoots, packedRoots, Roots.set] using bound1)
      (by simpa [cleanupRoots, headCleanupRoots, packedRoots, Roots.set] using bound2)
      (by simpa [cleanupRoots, headCleanupRoots, packedRoots, Roots.set] using bound3)
      supportAfter (fun slot member => branchMachine.zero slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto))
      empty3After outputAfter
  exact ⟨branchWorld, branchActive, _, final, after, cell, returnCost, branchRun, returned, empty, separate, fresh, kept⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
