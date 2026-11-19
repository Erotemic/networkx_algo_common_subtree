module

public import SubtreeProofs.Rust.SourceEmptyReturn

/-! Construct every instruction and return of the pinned shared empty-query
miss branch from the initialized native miss scope. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem empty_branch_complete {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [1, 2, 13] world active)
    {left right : BalancedWord} {table : MemoTable} (scope : MissScope initial left right table world active)
    (unbound : ∀ slot, slot ∉ [1, 2, 3] → initial.roots slot = none) (count : 27 ≤ active.count) :
    ∃ fuel budget final after cell cost,
      Calling.exec (Recursive.original budget fuel) callers emptyLeft world active =
        some (.returned final after (cell, encodeOutput (some emptyWitness) (.Entry ⟨left, right, emptyWitness⟩ table)), cost) ∧
      (∀ slot, after.state slot = .empty) ∧ after.RootsSeparate callers ∧
      (∀ slot binding, after.roots slot = some binding → before.memory.length ≤ binding.address) ∧
      Preserves before final previous.reads := by
  obtain ⟨fuel, budget, wi, ai, mi, inserted, insertion⟩ := empty_insertion_prefix_complete h scope unbound (by omega)
  let callee := Recursive.original budget fuel
  obtain ⟨wr, ar, retirement, mr, rootsR, countR, memoryR, witnessR, tableR, empty0R, empty3R, tupleR, ⟨root0, bound0R, raw0R⟩⟩ :=
    empty_insert_retire_complete mi callee inserted
  have unboundR : ∀ slot ∈ [24, 25, 26], ar.roots slot = none := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;>
      rw [rootsR, emptyArgumentRetired] <;> simp [Roots.set] <;>
      rw [inserted.otherRoots _ (by decide), scope.otherRoots _ (by decide)] <;> exact unbound _ (by decide)
  obtain ⟨wp, ap, root24, root26, packing, mp, countP, bound24P, retired25P, bound26P, otherP,
    outputP, empty16P, empty18P, empty24P, empty26P⟩ :=
    empty_return_packing_complete mr callee emptyWitness (.Entry ⟨left, right, emptyWitness⟩ table)
      witnessR tableR bound0R raw0R empty0R (by rw [countR, inserted.count]; exact count) unboundR
  have bound0P : ap.roots 0 = some root0 := by rw [otherP 0 (by decide)]; exact bound0R
  have oldRoots : ∀ slot ∈ [1, 2, 3, 13, 16, 18], ap.roots slot = ai.roots slot := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [otherP _ (by decide), rootsR, emptyArgumentRetired] <;> simp [Roots.set]
  have boundOld : ∀ slot ∈ [1, 2, 3, 13], ∃ binding, active.roots slot = some binding := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact Activation.root_of_materialize h.native.valid (value := .reference (encodeWord left)) (by rw [scope.inputs.left]; simp only [Slot.materialize])
    · exact Activation.root_of_materialize h.native.valid (value := .reference (encodeWord right)) (by rw [scope.inputs.right]; simp only [Slot.materialize])
    · exact Activation.root_of_materialize h.native.valid (by rw [scope.inputs.table]; exact Slot.materialize_ofValue _)
    · exact scope.tupleRoot
  have bound : ∀ slot ∈ emptyCleanupSlots, ∃ binding, ap.roots slot = some binding := by
    intro slot member
    simp only [emptyCleanupSlots, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rest
    · exact ⟨root26, bound26P⟩
    · exact ⟨root24, bound24P⟩
    · rw [oldRoots 18 (by simp)]; exact inserted.live 18 (by simp)
    · rw [oldRoots 16 (by simp)]; exact inserted.live 16 (by simp)
    · have old : slot ∈ [1, 2, 3, 13] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto
      rw [oldRoots slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at old ⊢; tauto),
        inserted.otherRoots slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at old ⊢; rcases old with rfl | rfl | rfl | rfl <;> decide)]
      exact boundOld slot old
  have empty3P : ap.state 3 = .empty :=
    (packing.closed_local_same (index := 3) mr.native.valid mr.native.callersValid mr.native.wellFormed
      (by rw [empty3R]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans empty3R
  have zero : ∀ slot ∈ emptyCleanupSlots, (ap.state slot).dropWork.boxes = 0 := by
    intro slot member
    simp only [emptyCleanupSlots, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [empty26P]; simp only [Slot.dropWork]
    · rw [empty24P]; simp only [Slot.dropWork]
    · rw [empty18P]; simp only [Slot.dropWork]
    · rw [empty16P]; simp only [Slot.dropWork]
    · exact mp.zero 13 (by simp)
    · rw [empty3P]; simp only [Slot.dropWork]
    · exact mp.zero 2 (by simp)
    · exact mp.zero 1 (by simp)
  have support : ∀ slot, slot ≠ 0 → slot ∉ emptyCleanupSlots → ap.roots slot = none := by
    intro slot nonzero outside
    by_cases retired : slot ∈ [17, 19, 20, 21, 22, 23, 25]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at retired
      rcases retired with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [otherP 17 (by decide), rootsR, emptyArgumentRetired]; simpa [Roots.set] using inserted.retired17
      · rw [otherP 19 (by decide), rootsR]; simp [emptyArgumentRetired, Roots.set]
      · rw [otherP 20 (by decide), rootsR]; simp [emptyArgumentRetired, Roots.set]
      · rw [otherP 21 (by decide), rootsR]; simp [emptyArgumentRetired, Roots.set]
      · rw [otherP 22 (by decide), rootsR]; simp [emptyArgumentRetired, Roots.set]
      · rw [otherP 23 (by decide), rootsR]; simp [emptyArgumentRetired, Roots.set]
      · exact retired25P
    · have notCreated : slot ∉ [16, 17, 18, 19, 20, 21, 22, 23] := by
        simp only [emptyCleanupSlots, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside retired ⊢; tauto
      have notPacked : slot ∉ [24, 25, 26] := by
        simp only [emptyCleanupSlots, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside retired ⊢; tauto
      rw [otherP slot notPacked, rootsR]
      have rootsSame : emptyArgumentRetired ai.roots slot = ai.roots slot := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at notCreated
        simp only [emptyArgumentRetired, Roots.set, notCreated.2.2.2.1, notCreated.2.2.2.2.1,
          notCreated.2.2.2.2.2.1, notCreated.2.2.2.2.2.2.1, notCreated.2.2.2.2.2.2.2, ite_false]
      rw [rootsSame, inserted.otherRoots slot notCreated, scope.otherRoots slot (by
        simp only [emptyCleanupSlots, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto)]
      apply unbound slot
      simp only [emptyCleanupSlots, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto
  obtain ⟨final, after, cell, last, cleanup, empty, separate, fresh, kept⟩ :=
    empty_cleanup_return_complete mp callee bound0P bound zero support outputP
  obtain ⟨packingCost, packed⟩ := packing.exec cleanup
  obtain ⟨retirementCost, retired⟩ := retirement.exec packed
  obtain ⟨cost, whole⟩ := (insertion fuel budget (by rfl) (by rfl)).exec retired
  refine ⟨fuel, budget, final, after, cell, cost, ?_, empty, separate, fresh, kept⟩
  rw [emptyLeft_actions]
  exact whole

end SubtreeProofs.Rust.SourceEval.Evaluator
