module

public import SubtreeProofs.Rust.SourcePairLeftFreshEntry
public import SubtreeProofs.Rust.SourceRootOverflowProgram

/-! Actual left-failure packing, candidate/query cleanup and root presence. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def leftFailureCleanupActions : List Action :=
  [.storageDead 81, .drop 75, .storageDead 75, .drop 74, .storageDead 74,
    .drop 71, .storageDead 71, .drop 64, .storageDead 64]

theorem cleanupLeft_actions : cleanupLeft = leftFailureCleanupActions.foldr Control.Tree.step .done := rfl

theorem leftFailure_actions : leftFailure = (failurePackActions 75 83 84).foldr Control.Tree.step .done := rfl

def pairLeftLiveRoots : List Nat := pairTailLiveRoots ++ [51, 58, 64, 71, 74, 75, 81]

theorem pair_left_root_presence {callee : Derived.Callees} {callers : List Activation}
    {world final : World} {active after : Activation}
    (present : rootPresence active.roots = fun slot => pairRootScoreLiveRoots.contains slot)
    (steps : Calling.Prefix callee callers matchedCases matchedActions world active final after) :
    rootPresence after.roots = fun slot => pairLeftLiveRoots.contains slot := by
  rw [steps.root_presence, present, rootPresence_fold_contains]
  have same : (matchedActions.foldl rootSlotsStep pairRootScoreLiveRoots).Perm pairLeftLiveRoots := by decide +kernel
  funext slot
  exact Bool.eq_iff_iff.mpr (by simpa only [List.contains_iff_mem] using same.mem_iff)

end SubtreeProofs.Rust.SourceEval.Evaluator
