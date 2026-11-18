module

public import SubtreeProofs.Rust.SourceLeftFailureProgram
public import SubtreeProofs.Rust.SourcePairFailureOuterReturn

/-! Drop the held concatenated query and matched candidate on left failure.
Both independent owner bounds are used before their storage retirement. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem left_failure_cleanup_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees)
    (present : rootPresence active.roots = fun slot => pairLeftLiveRoots.contains slot) (count : 113 ≤ active.count)
    (zero : ∀ slot ∈ [74, 75, 81], (active.state slot).dropWork.boxes = 0)
    (held : ∀ slot ∈ [64, 71], LocalOwnersAbove before.memory.length world active slot)
    {table : MemoTable} (output : active.state 0 = Slot.ofValue (encodeOutput none table)) :
    ∃ final after,
      Calling.Prefix callee callers .done leftFailureCleanupActions world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      rootPresence after.roots = (fun slot => (pairTailLiveRoots ++ [51, 58]).contains slot) ∧
      after.state 0 = Slot.ofValue (encodeOutput none table) ∧ after.count = active.count := by
  have ready : retirementReady (rootPresence active.roots) leftFailureCleanupActions = true := by rw [present]; decide +kernel
  have fresh : ∀ slot, Action.drop slot ∈ leftFailureCleanupActions ∨ Action.storageDead slot ∈ leftFailureCleanupActions →
      LocalOwnersAbove before.memory.length world active slot := by
    intro slot member
    by_cases candidate : slot = 64
    · subst slot; exact held 64 (by simp)
    by_cases query : slot = 71
    · subst slot; exact held 71 (by simp)
    apply LocalOwnersAbove.of_zero (zero slot ?_)
    simp [leftFailureCleanupActions] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have checks : retirementZeroChecks (fun slot => (active.state slot).dropWork.boxes) leftFailureCleanupActions := by
    simp only [leftFailureCleanupActions, retirementZeroChecks, clearBoxCount]
    simp only [Nat.reduceEqDiff, ite_true, ite_false]
    exact ⟨zero 81 (by simp), trivial, trivial, trivial, trivial, trivial⟩
  obtain ⟨final, after, steps, machine, _, countAfter, _⟩ :=
    (RetirementPlan.of_presence ready).complete_fresh callee .done h rfl
      (by intro slot member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega) fresh checks
  have presence : rootPresence after.roots = fun slot => (pairTailLiveRoots ++ [51, 58]).contains slot := by
    rw [steps.root_presence, present, rootPresence_fold_contains]
    have same : (leftFailureCleanupActions.foldl rootSlotsStep pairLeftLiveRoots).Perm (pairTailLiveRoots ++ [51, 58]) := by decide +kernel
    funext slot
    exact Bool.eq_iff_iff.mpr (by simpa only [List.contains_iff_mem] using same.mem_iff)
  have outputAfter := (steps.closed_local_same_calls
    (by rw [output]; exact ofValue_typed (encodeOutput_typed none table))
    (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (by decide +kernel)).trans output
  exact ⟨final, after, steps, machine, presence, outputAfter, countAfter⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
