module

public import SubtreeProofs.Rust.SourceTailFailureProgram
public import SubtreeProofs.Rust.SourcePairScoreFreshEntry
public import SubtreeProofs.Rust.SourceRetirementMaskCounts
public import SubtreeProofs.Rust.SourceEmptyRootStorage

/-! The pinned subtotal-overflow branch and its exact scalar-result storage.
Failure packing retains its actual trailing storage-dead continuation. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def subtotalCleanupActions : List Action := [.storageDead 51, .drop 47]

theorem cleanupTails_actions : cleanupTails = subtotalCleanupActions.foldr Control.Tree.step .done := rfl

def subtotalOverflowActions : List Action := failurePackActions 42 56 57 ++ [.storageDead 52]

theorem subtotalOverflow_actions : subtotalOverflow = subtotalOverflowActions.foldr Control.Tree.step .done := rfl

def pairScoreLiveRoots : List Nat := pairTailLiveRoots ++ [51, 52]

theorem pair_score_root_presence {callee : Derived.Callees} {callers : List Activation}
    {world final : World} {active after : Activation}
    (present : rootPresence active.roots = fun slot => pairTailLiveRoots.contains slot)
    (steps : Calling.Prefix callee callers scoreCases scoreActions world active final after) :
    rootPresence after.roots = fun slot => pairScoreLiveRoots.contains slot := by
  rw [steps.root_presence, present, rootPresence_fold_contains]
  have same : (scoreActions.foldl rootSlotsStep pairTailLiveRoots).Perm pairScoreLiveRoots := by decide +kernel
  funext slot
  exact Bool.eq_iff_iff.mpr (by simpa only [List.contains_iff_mem] using same.mem_iff)

theorem number_option_zero (result : Option Nat) : (Slot.ofValue (encodeNumberOption result)).dropWork.boxes = 0 := by
  cases result <;> simp [encodeNumberOption, Slot.ofValue, ofFields, Slot.dropWork, dropFields, DropWork.plus]

theorem subtotal_overflow_pack_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) {heads tails : CommonEmbedding} {table : MemoTable}
    (scope : ScoreSumScope heads tails table world active) (storage : EmptyRootStorage world active 0)
    (present : rootPresence active.roots = fun slot => pairScoreLiveRoots.contains slot) (count : 113 ≤ active.count) :
    ∃ final after,
      Calling.Prefix callee callers .done subtotalOverflowActions world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      rootPresence after.roots = (fun slot => (pairTailLiveRoots ++ [51]).contains slot) ∧
      after.state 0 = Slot.ofValue (encodeOutput none table) ∧ after.state 42 = .empty ∧ after.count = active.count := by
  obtain ⟨root0, bound0, raw0⟩ := storage.root
  obtain ⟨packed, packetActive, packing, packedMachine, packedRoots, packedCount, _, output0, empty42⟩ :=
    failure_pack_complete_with_suffix h callee (.step (.storageDead 52) .done) 42 56 57
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by omega) (by omega)
      (rootPresence.absent present (by decide +kernel)) (rootPresence.absent present (by decide +kernel))
      scope.tableValue bound0 raw0 storage.empty
  have zero52 : (packetActive.state 52).dropWork.boxes = 0 := by
    rw [packing.boxes_same_calls (by decide +kernel), scope.result]
    exact number_option_zero _
  obtain ⟨binding, bound52⟩ := rootPresence.bound present (slot := 52) (by decide +kernel)
  have plan : RetirementPlan packetActive.roots [.storageDead 52] (packetActive.roots.set 52 none) :=
    .dead (binding := binding) (by rw [packedRoots]; exact bound52) (.nil _)
  obtain ⟨final, after, retired, machine, _, countAfter, _⟩ := plan.complete_original callee .done packedMachine rfl (by
    intro slot member
    have same : slot = 52 := by simpa using member
    subst slot
    exact zero52)
  have whole : Calling.Prefix callee callers .done subtotalOverflowActions world active final after :=
    Calling.Prefix.append (suffix := .done) (rest := [.storageDead 52]) packing retired
  have finalPresence : rootPresence after.roots = fun slot => (pairTailLiveRoots ++ [51]).contains slot := by
    rw [whole.root_presence, present, rootPresence_fold_contains]
    have same : (subtotalOverflowActions.foldl rootSlotsStep pairScoreLiveRoots).Perm (pairTailLiveRoots ++ [51]) := by decide +kernel
    funext slot
    exact Bool.eq_iff_iff.mpr (by simpa only [List.contains_iff_mem] using same.mem_iff)
  have outputAfter := (retired.closed_local_same_calls
    (by rw [output0]; exact ofValue_typed (encodeOutput_typed none table))
    (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (by decide +kernel)).trans output0
  exact ⟨final, after, whole, machine, finalPresence, outputAfter,
    retired.empty_untouched empty42 (by decide +kernel), countAfter.trans packedCount⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
