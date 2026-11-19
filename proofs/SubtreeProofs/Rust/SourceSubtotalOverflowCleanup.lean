module

public import SubtreeProofs.Rust.SourceSubtotalOverflowProgram
public import SubtreeProofs.Rust.SourceTailFailureCleanup

/-! Actual subtotal-overflow cleanup retires the scalar subtotal and both
fresh recursive witnesses before the shared input cleanup. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem subtotal_overflow_cleanup_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees)
    (present : rootPresence active.roots = fun slot => (pairTailLiveRoots ++ [51]).contains slot)
    (count : 113 ≤ active.count)
    (zero : ∀ slot ∈ tailFailureZeroSlots, slot ≠ 47 → (active.state slot).dropWork.boxes = 0)
    (zero51 : (active.state 51).dropWork.boxes = 0)
    (headsFresh : LocalOwnersAbove before.memory.length world active 37)
    (tailsFresh : LocalOwnersAbove before.memory.length world active 47)
    (empty3 : active.state 3 = .empty) {table : MemoTable}
    (output : active.state 0 = Slot.ofValue (encodeOutput none table)) :
    ∃ tailWorld tailActive headWorld headActive final after,
      Calling.Prefix callee callers .done subtotalCleanupActions world active tailWorld tailActive ∧
      Calling.Prefix callee callers .done tailFailureCleanupActions tailWorld tailActive headWorld headActive ∧
      Calling.Prefix callee callers .done headCleanupActions headWorld headActive final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      rootPresence after.roots = (fun slot => [0, 1, 2, 3].contains slot) ∧
      after.state 0 = Slot.ofValue (encodeOutput none table) ∧ after.state 3 = .empty ∧ after.count = active.count := by
  have ready : retirementReady (rootPresence active.roots) subtotalCleanupActions = true := by rw [present]; decide +kernel
  have fresh : ∀ slot, Action.drop slot ∈ subtotalCleanupActions ∨ Action.storageDead slot ∈ subtotalCleanupActions →
      LocalOwnersAbove before.memory.length world active slot := by
    intro slot member
    simp [subtotalCleanupActions, Action.drop.injEq,
      Action.storageDead.injEq, reduceCtorEq] at member
    rcases member with rfl | rfl
    · exact tailsFresh
    · exact .of_zero zero51
  have checks : retirementZeroChecks (fun slot => (active.state slot).dropWork.boxes) subtotalCleanupActions := by
    exact ⟨zero51, trivial⟩
  obtain ⟨tailWorld, tailActive, cleanup, tailMachine, _, tailCount, _⟩ :=
    (RetirementPlan.of_presence ready).complete_fresh callee .done h rfl
      (by intro slot member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega) fresh checks
  have presentTail : rootPresence tailActive.roots = fun slot => pairTailLiveRoots.contains slot := by
    rw [cleanup.root_presence, present, rootPresence_fold_contains]
    have same : (subtotalCleanupActions.foldl rootSlotsStep (pairTailLiveRoots ++ [51])).Perm pairTailLiveRoots := by decide +kernel
    funext slot
    exact Bool.eq_iff_iff.mpr (by simpa only [List.contains_iff_mem] using same.mem_iff)
  have counts := cleanup.retirement_boxes h.native.valid h.native.callersValid h.native.wellFormed (by
    intro act member
    simp only [subtotalCleanupActions, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨_, Or.inr rfl⟩
    · exact ⟨_, Or.inl rfl⟩)
  have tailZero : ∀ slot ∈ tailFailureZeroSlots, (tailActive.state slot).dropWork.boxes = 0 := by
    intro slot member
    by_cases selected : slot = 47
    · subst slot
      rw [congrFun counts 47]
      simp [subtotalCleanupActions, retirementBoxStep, clearBoxCount]
    · have different : slot ≠ 51 := by
        simp only [tailFailureZeroSlots, List.mem_cons, List.not_mem_nil, or_false] at member
        omega
      rw [congrFun counts slot]
      simpa [subtotalCleanupActions, retirementBoxStep, clearBoxCount, selected, different] using zero slot member selected
  have headFresh := cleanup.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by decide +kernel))
    h.native.valid h.native.callersValid h.native.wellFormed headsFresh
  have outputTail := (cleanup.closed_local_same_calls
    (by rw [output]; exact ofValue_typed (encodeOutput_typed none table))
    (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (by decide +kernel)).trans output
  obtain ⟨headWorld, headActive, final, after, headCleanup, inputsCleanup, machine, presence, outputAfter, emptyAfter, finalCount⟩ :=
    tail_failure_cleanup_complete tailMachine callee presentTail (by omega) tailZero headFresh
      (cleanup.empty_untouched empty3 (by decide +kernel)) outputTail
  exact ⟨tailWorld, tailActive, headWorld, headActive, final, after, cleanup, headCleanup, inputsCleanup,
    machine, presence, outputAfter, emptyAfter, finalCount.trans tailCount⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
