module

public import SubtreeProofs.Rust.SourceTailFailureProgram
public import SubtreeProofs.Rust.SourceRetirementMaskCounts

/-! Construct tail/head cleanup after the updated table has moved to output.
The held head witness is dropped through its independently derived owner bound. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def tailFailureZeroSlots : List Nat := [1, 2, 3, 13, 27, 28, 29, 30, 31, 32, 41, 42, 47]

theorem tail_failure_cleanup_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees)
    (present : rootPresence active.roots = fun slot => pairTailLiveRoots.contains slot)
    (count : 113 ≤ active.count)
    (zero : ∀ slot ∈ tailFailureZeroSlots, (active.state slot).dropWork.boxes = 0)
    (headsFresh : LocalOwnersAbove before.memory.length world active 37)
    (empty3 : active.state 3 = .empty) {table : MemoTable}
    (output : active.state 0 = Slot.ofValue (encodeOutput none table)) :
    ∃ middle current final after,
      Calling.Prefix callee callers .done tailFailureCleanupActions world active middle current ∧
      Calling.Prefix callee callers .done headCleanupActions middle current final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      rootPresence after.roots = (fun slot => [0, 1, 2, 3].contains slot) ∧
      after.state 0 = Slot.ofValue (encodeOutput none table) ∧ after.state 3 = .empty ∧ after.count = active.count := by
  have ready : retirementReady (rootPresence active.roots) tailFailureCleanupActions = true := by rw [present]; decide +kernel
  have fresh : ∀ slot, Action.drop slot ∈ tailFailureCleanupActions ∨ Action.storageDead slot ∈ tailFailureCleanupActions →
      LocalOwnersAbove before.memory.length world active slot := by
    intro slot member
    by_cases selected : slot = 37
    · subst slot; exact headsFresh
    · apply LocalOwnersAbove.of_zero (zero slot ?_)
      simp [tailFailureCleanupActions] at member
      simp only [tailFailureZeroSlots, List.mem_cons, List.not_mem_nil, or_false]
      omega
  have checks : retirementZeroChecks (fun slot => (active.state slot).dropWork.boxes) tailFailureCleanupActions := by
    simp only [tailFailureCleanupActions, retirementZeroChecks, clearBoxCount]
    simp only [Nat.reduceEqDiff, ite_true, ite_false]
    exact ⟨zero 47 (by decide), trivial, trivial, trivial⟩
  obtain ⟨middle, current, cleanupTail, m1, _, count1, _⟩ := (RetirementPlan.of_presence ready).complete_fresh callee .done h rfl
    (by intro slot member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega) fresh checks
  have present1 : rootPresence current.roots = fun slot => ([0, 1, 2, 3, 13, 27, 28, 29, 30, 31, 32, 37] : List Nat).contains slot := by
    rw [cleanupTail.root_presence, present, rootPresence_fold_contains]
    have same : (tailFailureCleanupActions.foldl rootSlotsStep pairTailLiveRoots).Perm [0, 1, 2, 3, 13, 27, 28, 29, 30, 31, 32, 37] := by decide +kernel
    funext slot
    exact Bool.eq_iff_iff.mpr (by simpa only [List.contains_iff_mem] using same.mem_iff)
  have counts := cleanupTail.retirement_boxes h.native.valid h.native.callersValid h.native.wellFormed (by
    intro act member
    simp only [tailFailureCleanupActions, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact ⟨_, Or.inl rfl⟩ | exact ⟨_, Or.inr rfl⟩)
  have headZero : ∀ slot ∈ [13, 27, 28, 29, 30, 31, 32, 37], (current.state slot).dropWork.boxes = 0 := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (rw [congrFun counts 37]; simp [tailFailureCleanupActions, retirementBoxStep, clearBoxCount])
      | (rw [cleanupTail.boxes_same_calls (by decide +kernel)]; exact zero _ (by decide +kernel))
  have readyHead : retirementReady (rootPresence current.roots) headCleanupActions = true := by rw [present1]; decide +kernel
  have zeroHead : ZeroRetirement headCleanupActions current.state := by
    intro slot member
    apply headZero slot
    simp [headCleanupActions] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  obtain ⟨final, after, cleanupHead, m2, _, count2, _⟩ := (RetirementPlan.of_presence readyHead).complete_original callee .done m1 rfl zeroHead
  have present2 : rootPresence after.roots = fun slot => [0, 1, 2, 3].contains slot := by
    rw [cleanupHead.root_presence, present1, rootPresence_fold_contains]
    have same : (headCleanupActions.foldl rootSlotsStep [0, 1, 2, 3, 13, 27, 28, 29, 30, 31, 32, 37]).Perm [0, 1, 2, 3] := by decide +kernel
    funext slot
    exact Bool.eq_iff_iff.mpr (by simpa only [List.contains_iff_mem] using same.mem_iff)
  have output1 := (cleanupTail.closed_local_same_calls
    (by rw [output]; exact ofValue_typed (encodeOutput_typed none table))
    (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (by decide +kernel)).trans output
  have output2 := (cleanupHead.closed_local_same_calls
    (by rw [output1]; exact ofValue_typed (encodeOutput_typed none table))
    (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (by decide +kernel)).trans output1
  exact ⟨middle, current, final, after, cleanupTail, cleanupHead, m2, present2, output2,
    cleanupHead.empty_untouched (cleanupTail.empty_untouched empty3 (by decide +kernel)) (by decide +kernel), count2.trans count1⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
