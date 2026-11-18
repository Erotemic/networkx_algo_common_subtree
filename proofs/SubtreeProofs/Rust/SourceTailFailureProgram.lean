module

public import SubtreeProofs.Rust.SourceHeadFailureCleanup
public import SubtreeProofs.Rust.SourcePairTailFreshScope
public import SubtreeProofs.Rust.SourceRootPresence

/-! The actual tail-failure pack/cleanup and the exact physical storage at the
tail-result switch, derived from parsed entry and four real prefixes. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def tailFailureCleanupActions : List Action :=
  [.storageDead 47, .drop 42, .storageDead 42, .drop 41, .storageDead 41, .drop 37]

theorem tailsFailure_actions : tailsFailure = (failurePackActions 42 49 50).foldr Control.Tree.step .done := rfl

theorem cleanupHeads_actions : cleanupHeads = tailFailureCleanupActions.foldr Control.Tree.step .done := rfl

def pairTailLiveRoots : List Nat := [0, 1, 2, 3, 13, 27, 28, 29, 30, 31, 32, 37, 41, 42, 47]

theorem pair_tail_root_presence {callee : Derived.Callees}
    {world entered lookupWorld missWorld headWorld final : World}
    {active lookupActive missActive headActive after : Activation} {callers : List Activation}
    {frame count : Nat} {packets : List ValueCell}
    (entryRun : enter world frame count packets = some (entered, active)) (arity : packets.length = 3)
    (common : Calling.Prefix callee callers lookupSwitch commonPrefix entered active lookupWorld lookupActive)
    (setup : Calling.Prefix callee callers missCases missSetupActions lookupWorld lookupActive missWorld missActive)
    (head : Calling.Prefix callee callers headCases headActions missWorld missActive headWorld headActive)
    (tail : Calling.Prefix callee callers tailCases tailActions headWorld headActive final after) :
    rootPresence after.roots = fun slot => pairTailLiveRoots.contains slot := by
  rw [tail.root_presence, head.root_presence, setup.root_presence, common.root_presence, enter_root_presence entryRun, arity]
  have initial : (fun slot => decide (0 < slot ∧ slot ≤ 3)) = fun slot => [1, 2, 3].contains slot := by
    funext slot
    simp only [List.contains_cons, List.contains_nil, Bool.or_false]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
    omega
  rw [initial]
  change (commonPrefix ++ missSetupActions ++ headActions ++ tailActions).foldl rootPresenceStep
    (fun slot => [1, 2, 3].contains slot) = _
  rw [rootPresence_fold_contains]
  have same : ((commonPrefix ++ missSetupActions ++ headActions ++ tailActions).foldl rootSlotsStep [1, 2, 3]).Perm pairTailLiveRoots := by
    decide +kernel
  funext slot
  exact Bool.eq_iff_iff.mpr (by simpa only [List.contains_iff_mem] using same.mem_iff)

end SubtreeProofs.Rust.SourceEval.Evaluator
