module

public import SubtreeProofs.Rust.SourceRootPresence
public import SubtreeProofs.Rust.SourcePairReturnStorage
public import SubtreeProofs.Rust.SourcePairFinishProgram

/-! Actual parsed entry and the eight constructed pair/pair prefixes determine
all older physical roots. Logical holes and moved-out values retain storage. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def pairRightLiveRoots : List Nat :=
  [0, 1, 2, 3, 13, 27, 28, 29, 30, 31, 32, 37, 41, 42, 47, 51, 58,
    64, 71, 74, 75, 81, 85, 88, 89, 95]

def pairRightRootActions : List Action := commonPrefix ++ missSetupActions ++ headActions ++ tailActions ++
  scoreActions ++ rootScoreActions ++ matchedActions ++ rightActions

theorem pair_right_root_slots : (pairRightRootActions.foldl rootSlotsStep [1, 2, 3]).Perm pairRightLiveRoots := by
  decide +kernel

theorem pair_right_root_presence (fuel budget : Nat)
    {world entered lookupWorld missWorld headWorld tailWorld scoreWorld rootWorld leftWorld final : World}
    {active lookupActive missActive headActive tailActive scoreActive rootActive leftActive after : Activation}
    {callers : List Activation} {frame count : Nat} {packets : List ValueCell}
    (entryRun : enter world frame count packets = some (entered, active)) (arity : packets.length = 3)
    (common : Calling.Prefix (Recursive.original budget fuel) callers lookupSwitch commonPrefix entered active lookupWorld lookupActive)
    (setup : Calling.Prefix (Recursive.original budget fuel) callers missCases missSetupActions lookupWorld lookupActive missWorld missActive)
    (head : Calling.Prefix (Recursive.original budget fuel) callers headCases headActions missWorld missActive headWorld headActive)
    (tail : Calling.Prefix (Recursive.original budget fuel) callers tailCases tailActions headWorld headActive tailWorld tailActive)
    (score : Calling.Prefix (Recursive.original budget fuel) callers scoreCases scoreActions tailWorld tailActive scoreWorld scoreActive)
    (root : Calling.Prefix (Recursive.original budget fuel) callers rootScoreCases rootScoreActions scoreWorld scoreActive rootWorld rootActive)
    (left : Calling.Prefix (Recursive.original budget fuel) callers matchedCases matchedActions rootWorld rootActive leftWorld leftActive)
    (right : Calling.Prefix (Recursive.original budget fuel) callers rightContractionCases rightActions leftWorld leftActive final after) :
    rootPresence after.roots = fun slot => pairRightLiveRoots.contains slot := by
  rw [right.root_presence, left.root_presence, root.root_presence, score.root_presence,
    tail.root_presence, head.root_presence, setup.root_presence, common.root_presence,
    enter_root_presence entryRun, arity]
  have initial : (fun slot => decide (0 < slot ∧ slot ≤ 3)) = fun slot => [1, 2, 3].contains slot := by
    funext slot
    simp only [List.contains_cons, List.contains_nil, Bool.or_false]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
    omega
  rw [initial]
  change pairRightRootActions.foldl rootPresenceStep (fun slot => [1, 2, 3].contains slot) = _
  rw [rootPresence_fold_contains]
  funext slot
  exact Bool.eq_iff_iff.mpr (by simpa only [List.contains_iff_mem] using pair_right_root_slots.mem_iff)

theorem pair_finish_56_root_presence {callee : Derived.Callees} {callers : List Activation}
    {world final : World} {active after : Activation}
    (present : rootPresence active.roots = fun slot => pairRightLiveRoots.contains slot)
    (steps : Calling.Prefix callee callers (finishCode 56) (finishActions.take 56) world active final after) :
    rootPresence after.roots = fun slot => pairRightLiveRoots.contains slot := by
  rw [steps.root_presence, present]
  rw [rootPresence_fold_contains]
  have same : ((finishActions.take 56).foldl rootSlotsStep pairRightLiveRoots).Perm pairRightLiveRoots := by
    decide +kernel
  funext slot
  exact Bool.eq_iff_iff.mpr (by simpa only [List.contains_iff_mem] using same.mem_iff)

end SubtreeProofs.Rust.SourceEval.Evaluator
