module

public import SubtreeProofs.Rust.SourceRightFailureProgram

/-! Construct right-query and left-witness destruction. Exact actual mask
counts derive zero owners in retained root81 before the outer storage-dead. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem right_failure_cleanup_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees)
    (present : rootPresence active.roots = fun slot => pairRightLiveRoots.contains slot) (count : 113 ≤ active.count)
    (zero : ∀ slot ∈ [88, 89, 95], (active.state slot).dropWork.boxes = 0)
    (held : ∀ slot ∈ [81, 85], LocalOwnersAbove before.memory.length world active slot)
    {table : MemoTable} (output : active.state 0 = Slot.ofValue (encodeOutput none table)) :
    ∃ final after,
      Calling.Prefix callee callers .done rightFailureCleanupActions world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      rootPresence after.roots = (fun slot => pairLeftLiveRoots.contains slot) ∧
      after.state 0 = Slot.ofValue (encodeOutput none table) ∧
      (after.state 81).dropWork.boxes = 0 ∧ after.count = active.count := by
  have ready : retirementReady (rootPresence active.roots) rightFailureCleanupActions = true := by rw [present]; decide +kernel
  have fresh : ∀ slot, Action.drop slot ∈ rightFailureCleanupActions ∨ Action.storageDead slot ∈ rightFailureCleanupActions →
      LocalOwnersAbove before.memory.length world active slot := by
    intro slot member
    by_cases leftWitness : slot = 81
    · subst slot; exact held 81 (by simp)
    by_cases rightQuery : slot = 85
    · subst slot; exact held 85 (by simp)
    apply LocalOwnersAbove.of_zero (zero slot ?_)
    simp [rightFailureCleanupActions] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have checks : retirementZeroChecks (fun slot => (active.state slot).dropWork.boxes) rightFailureCleanupActions := by
    simp only [rightFailureCleanupActions, retirementZeroChecks, clearBoxCount]
    simp only [Nat.reduceEqDiff, ite_true, ite_false]
    exact ⟨zero 95 (by simp), by decide⟩
  obtain ⟨final, after, steps, machine, _, countAfter, _⟩ :=
    (RetirementPlan.of_presence ready).complete_fresh callee .done h rfl
      (by intro slot member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega) fresh checks
  have presence : rootPresence after.roots = fun slot => pairLeftLiveRoots.contains slot := by
    rw [steps.root_presence, present, rootPresence_fold_contains]
    have same : (rightFailureCleanupActions.foldl rootSlotsStep pairRightLiveRoots).Perm pairLeftLiveRoots := by decide +kernel
    funext slot
    exact Bool.eq_iff_iff.mpr (by simpa only [List.contains_iff_mem] using same.mem_iff)
  have counts := steps.retirement_boxes h.native.valid h.native.callersValid h.native.wellFormed (by
    intro act member
    simp only [rightFailureCleanupActions, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact ⟨_, Or.inl rfl⟩ | exact ⟨_, Or.inr rfl⟩)
  have zero81 : (after.state 81).dropWork.boxes = 0 := by
    rw [congrFun counts 81]
    simp [rightFailureCleanupActions, retirementBoxStep, clearBoxCount]
  have outputAfter := (steps.closed_local_same_calls
    (by rw [output]; exact ofValue_typed (encodeOutput_typed none table))
    (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (by decide +kernel)).trans output
  exact ⟨final, after, steps, machine, presence, outputAfter, zero81, countAfter⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
