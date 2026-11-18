module

public import SubtreeProofs.Rust.SourceSubtotalOverflowProgram
public import SubtreeProofs.Rust.SourcePairRootScoreFreshEntry

/-! The actual root-overflow arm keeps its trailing scalar retirement.
Root presence follows from the checked root-score prefix. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def rootCleanupActions : List Action := [.storageDead 58]

theorem cleanupSubtotal_actions : cleanupSubtotal = rootCleanupActions.foldr Control.Tree.step .done := rfl

def rootOverflowActions : List Action := failurePackActions 42 62 63 ++ [.storageDead 59]

theorem rootOverflow_actions : rootOverflow = rootOverflowActions.foldr Control.Tree.step .done := rfl

def pairRootScoreLiveRoots : List Nat := pairTailLiveRoots ++ [51, 58, 59]

theorem pair_root_score_root_presence {callee : Derived.Callees} {callers : List Activation}
    {world final : World} {active after : Activation}
    (present : rootPresence active.roots = fun slot => pairScoreLiveRoots.contains slot)
    (steps : Calling.Prefix callee callers rootScoreCases rootScoreActions world active final after) :
    rootPresence after.roots = fun slot => pairRootScoreLiveRoots.contains slot := by
  rw [steps.root_presence, present, rootPresence_fold_contains]
  have same : (rootScoreActions.foldl rootSlotsStep pairScoreLiveRoots).Perm pairRootScoreLiveRoots := by decide +kernel
  funext slot
  exact Bool.eq_iff_iff.mpr (by simpa only [List.contains_iff_mem] using same.mem_iff)

theorem root_overflow_pack_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) {heads tails : CommonEmbedding} {table : MemoTable} {subtotal : Aeneas.Std.U32}
    (scope : RootScoreScope heads tails table subtotal world active) (storage : EmptyRootStorage world active 0)
    (present : rootPresence active.roots = fun slot => pairRootScoreLiveRoots.contains slot) (count : 113 ≤ active.count) :
    ∃ final after,
      Calling.Prefix callee callers .done rootOverflowActions world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      rootPresence after.roots = (fun slot => (pairTailLiveRoots ++ [51, 58]).contains slot) ∧
      after.state 0 = Slot.ofValue (encodeOutput none table) ∧ after.state 42 = .empty ∧ after.count = active.count := by
  obtain ⟨root0, bound0, raw0⟩ := storage.root
  obtain ⟨packed, packetActive, packing, packedMachine, packedRoots, packedCount, _, output0, empty42⟩ :=
    failure_pack_complete_with_suffix h callee (.step (.storageDead 59) .done) 42 62 63
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by omega) (by omega)
      (rootPresence.absent present (by decide +kernel)) (rootPresence.absent present (by decide +kernel))
      scope.tableValue bound0 raw0 storage.empty
  have zero59 : (packetActive.state 59).dropWork.boxes = 0 := by
    rw [packing.boxes_same_calls (by decide +kernel), scope.result]
    exact number_option_zero _
  obtain ⟨binding, bound59⟩ := rootPresence.bound present (slot := 59) (by decide +kernel)
  have plan : RetirementPlan packetActive.roots [.storageDead 59] (packetActive.roots.set 59 none) :=
    .dead (binding := binding) (by rw [packedRoots]; exact bound59) (.nil _)
  obtain ⟨final, after, retired, machine, _, countAfter, _⟩ := plan.complete_original callee .done packedMachine rfl (by
    intro slot member
    have same : slot = 59 := by simpa using member
    subst slot
    exact zero59)
  have whole : Calling.Prefix callee callers .done rootOverflowActions world active final after :=
    Calling.Prefix.append (suffix := .done) (rest := [.storageDead 59]) packing retired
  have finalPresence : rootPresence after.roots = fun slot => (pairTailLiveRoots ++ [51, 58]).contains slot := by
    rw [whole.root_presence, present, rootPresence_fold_contains]
    have same : (rootOverflowActions.foldl rootSlotsStep pairRootScoreLiveRoots).Perm (pairTailLiveRoots ++ [51, 58]) := by decide +kernel
    funext slot
    exact Bool.eq_iff_iff.mpr (by simpa only [List.contains_iff_mem] using same.mem_iff)
  have outputAfter := (retired.closed_local_same_calls
    (by rw [output0]; exact ofValue_typed (encodeOutput_typed none table))
    (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (by decide +kernel)).trans output0
  exact ⟨final, after, whole, machine, finalPresence, outputAfter,
    retired.empty_untouched empty42 (by decide +kernel), countAfter.trans packedCount⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
