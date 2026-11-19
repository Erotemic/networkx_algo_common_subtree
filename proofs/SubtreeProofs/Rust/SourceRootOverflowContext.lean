module

public import SubtreeProofs.Rust.SourceTypedRootStorage
public import SubtreeProofs.Rust.SourceEvaluatorPrefixConstraints
public import SubtreeProofs.Rust.SourceRootOverflowProgram
public import SubtreeProofs.Rust.SourcePairOlderMasks

/-! Parsed common storage and the six actual prefixes derive empty return
storage at root overflow, independently of a desired post-frame. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_root_return_storage (fuel budget : Nat)
    {entered lookupWorld missWorld headWorld tailWorld scoreWorld rootWorld : World}
    {active lookupActive missActive headActive tailActive scoreActive rootActive : Activation}
    {callers : List Activation}
    (valid : active.Valid entered) (callersValid : ∀ caller ∈ callers, caller.Valid entered) (wellFormed : entered.WellFormed)
    (typed : LocalsTyped CallingCertificate.originalEvaluator.locals active.state)
    (common : Calling.Prefix (Recursive.original budget fuel) callers lookupSwitch commonPrefix entered active lookupWorld lookupActive)
    (setup : Calling.Prefix (Recursive.original budget fuel) callers missCases missSetupActions lookupWorld lookupActive missWorld missActive)
    (head : Calling.Prefix (Recursive.original budget fuel) callers headCases headActions missWorld missActive headWorld headActive)
    (tail : Calling.Prefix (Recursive.original budget fuel) callers tailCases tailActions headWorld headActive tailWorld tailActive)
    (score : Calling.Prefix (Recursive.original budget fuel) callers scoreCases scoreActions tailWorld tailActive scoreWorld scoreActive)
    (root : Calling.Prefix (Recursive.original budget fuel) callers rootScoreCases rootScoreActions scoreWorld scoreActive rootWorld rootActive) :
    TypedRootStorage CallingCertificate.originalEvaluator.locals callers rootWorld rootActive 0 := by
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
  exact c4.through_prefix respects sourceTyped root constraints.roots (List.all_eq_true.mp (by decide +kernel))

end SubtreeProofs.Rust.SourceEval.Evaluator
