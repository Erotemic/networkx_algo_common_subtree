module

public import SubtreeProofs.Rust.SourceTypedRootStorage
public import SubtreeProofs.Rust.SourceEvaluatorPrefixConstraints
public import SubtreeProofs.Rust.SourcePairRightProvenanceEntry

/-! The parsed common prefix opens return storage. The original checked action
constraints then carry its empty mask and actual bytes through head/tail, scores,
matched/left recursion and right recursion. No final storage premise is supplied. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_right_return_storage (fuel budget : Nat)
    {entered lookupWorld missWorld headWorld tailWorld scoreWorld rootWorld leftWorld final : World}
    {active lookupActive missActive headActive tailActive scoreActive rootActive leftActive after : Activation}
    {callers : List Activation}
    (valid : active.Valid entered) (callersValid : ∀ caller ∈ callers, caller.Valid entered) (wellFormed : entered.WellFormed)
    (typed : LocalsTyped CallingCertificate.originalEvaluator.locals active.state)
    (common : Calling.Prefix (Recursive.original budget fuel) callers lookupSwitch commonPrefix entered active lookupWorld lookupActive)
    (setup : Calling.Prefix (Recursive.original budget fuel) callers missCases missSetupActions lookupWorld lookupActive missWorld missActive)
    (head : Calling.Prefix (Recursive.original budget fuel) callers headCases headActions missWorld missActive headWorld headActive)
    (tail : Calling.Prefix (Recursive.original budget fuel) callers tailCases tailActions headWorld headActive tailWorld tailActive)
    (score : Calling.Prefix (Recursive.original budget fuel) callers scoreCases scoreActions tailWorld tailActive scoreWorld scoreActive)
    (root : Calling.Prefix (Recursive.original budget fuel) callers rootScoreCases rootScoreActions scoreWorld scoreActive rootWorld rootActive)
    (left : Calling.Prefix (Recursive.original budget fuel) callers matchedCases matchedActions rootWorld rootActive leftWorld leftActive)
    (right : Calling.Prefix (Recursive.original budget fuel) callers rightContractionCases rightActions leftWorld leftActive final after) :
    TypedRootStorage CallingCertificate.originalEvaluator.locals callers final after 0 := by
  have respects := Recursive.original_typed_respects budget fuel
  have sourceTyped := Types.original_run_typed fuel
  have constraints := evaluator_prefix_constraints
  change Calling.Prefix (Recursive.original budget fuel) callers lookupSwitch (.storageLive 0 :: commonPrefix.tail)
    entered active lookupWorld lookupActive at common
  have c0 := common.opens_typed_storage respects sourceTyped valid callersValid wellFormed typed
    (by change ∀ act ∈ commonPrefix, Types.ActionConstraints CallingCertificate.originalEvaluator.locals act; exact constraints.common)
    (List.all_eq_true.mp (by decide +kernel))
  have c1 := c0.through_prefix respects sourceTyped setup constraints.miss (List.all_eq_true.mp (by decide +kernel))
  have c2 := c1.through_prefix respects sourceTyped head constraints.heads (List.all_eq_true.mp (by decide +kernel))
  have c3 := c2.through_prefix respects sourceTyped tail constraints.tails (List.all_eq_true.mp (by decide +kernel))
  have c4 := c3.through_prefix respects sourceTyped score constraints.scores (List.all_eq_true.mp (by decide +kernel))
  have c5 := c4.through_prefix respects sourceTyped root constraints.roots (List.all_eq_true.mp (by decide +kernel))
  have c6 := c5.through_prefix respects sourceTyped left constraints.matched (List.all_eq_true.mp (by decide +kernel))
  exact c6.through_prefix respects sourceTyped right constraints.right (List.all_eq_true.mp (by decide +kernel))

end SubtreeProofs.Rust.SourceEval.Evaluator
