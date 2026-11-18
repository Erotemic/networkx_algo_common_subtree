module

public import SubtreeProofs.Rust.SourcePrefixMaskFacts
public import SubtreeProofs.Rust.SourceEvaluatorCleanupTypes
public import SubtreeProofs.Rust.SourcePairRootPresence

/-! The five older cleanup masks missing from the finish scope follow from
actual head/tail/score moves and a successful scalar copy. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

structure PairOlderMasks (active : Activation) : Prop where
  tableEmpty : active.state 3 = .empty
  headHole : active.state 31 = .node .optional 1 [.empty]
  headTableEmpty : active.state 32 = .empty
  tailHole : active.state 41 = .node .optional 1 [.empty]
  subtotalZero : (active.state 51).dropWork.boxes = 0

theorem PairOlderMasks.through_prefix {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {actions : List Action} {world final : World} {active after : Activation}
    (masks : PairOlderMasks active) (steps : Calling.Prefix callee callers suffix actions world active final after)
    (safe : ∀ slot ∈ [3, 31, 32, 41, 51], actions.all (LocalPreservation.action slot) = true) :
    PairOlderMasks after := by
  exact ⟨steps.empty_untouched masks.tableEmpty (safe 3 (by simp)),
    steps.optional_hole_untouched masks.headHole (safe 31 (by simp)),
    steps.empty_untouched masks.headTableEmpty (safe 32 (by simp)),
    steps.optional_hole_untouched masks.tailHole (safe 41 (by simp)),
    (steps.boxes_same_calls (safe 51 (by simp))).trans masks.subtotalZero⟩

theorem pair_root_older_masks (fuel budget : Nat)
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
    PairOlderMasks rootActive := by
  have respects := Recursive.original_typed_respects budget fuel
  have sourceTyped := Types.original_run_typed fuel
  have constraints := evaluator_prefix_constraints
  have c0 := common.typed_spec respects sourceTyped valid callersValid wellFormed typed constraints.common
  have c1 := setup.typed_spec respects sourceTyped c0.1 c0.2.1 c0.2.2.1 c0.2.2.2 constraints.miss
  have c2 := head.typed_spec respects sourceTyped c1.1 c1.2.1 c1.2.2.1 c1.2.2.2 constraints.heads
  have c3 := tail.typed_spec respects sourceTyped c2.1 c2.2.1 c2.2.2.1 c2.2.2.2 constraints.tails
  have c4 := score.typed_spec respects sourceTyped c3.1 c3.2.1 c3.2.2.1 c3.2.2.2 constraints.scores
  have table3 := Calling.Prefix.typed_move_empty respects sourceTyped
    (before := headActions.take 14) (rest := headActions.drop 15) (slot := 3) (destination := 36)
    head c1.1 c1.2.1 c1.2.2.1 c1.2.2.2
    (fun act member => constraints.heads act (List.mem_of_mem_take member)) (by decide) (by decide +kernel)
  have table32 := Calling.Prefix.typed_move_empty respects sourceTyped
    (before := tailActions.take 12) (rest := tailActions.drop 13) (slot := 32) (destination := 46)
    tail c2.1 c2.2.1 c2.2.2.1 c2.2.2.2
    (fun act member => constraints.tails act (List.mem_of_mem_take member)) (by decide) (by decide +kernel)
  have hole31 := Calling.Prefix.typed_optional_hole respects sourceTyped
    (before := tailActions.take 1) (rest := tailActions.drop 2) (slot := 31) (destination := 38)
    tail c2.1 c2.2.1 c2.2.2.1 c2.2.2.2
    (fun act member => constraints.tails act (List.mem_of_mem_take member)) evaluator_cleanup_optional_types.1
    (by decide) (by decide +kernel)
  have hole41 := Calling.Prefix.typed_optional_hole respects sourceTyped
    (before := scoreActions.take 1) (rest := scoreActions.drop 2) (slot := 41) (destination := 48)
    score c3.1 c3.2.1 c3.2.2.1 c3.2.2.2
    (fun act member => constraints.scores act (List.mem_of_mem_take member)) evaluator_cleanup_optional_types.2
    (by decide) (by decide +kernel)
  have zero51 := Calling.Prefix.typed_copy_zero respects sourceTyped
    (before := rootScoreActions.take 9) (rest := rootScoreActions.drop 10) (slot := 51) (destination := 60)
    root c4.1 c4.2.1 c4.2.2.1 c4.2.2.2
    (fun act member => constraints.roots act (List.mem_of_mem_take member)) (by decide) (by decide +kernel)
  have older : PairOlderMasks rootActive := by
    refine ⟨?_, ?_, ?_, ?_, zero51⟩
    · exact root.empty_untouched (score.empty_untouched (tail.empty_untouched table3 (by decide +kernel))
        (by decide +kernel)) (by decide +kernel)
    · exact root.optional_hole_untouched (score.optional_hole_untouched hole31 (by decide +kernel)) (by decide +kernel)
    · exact root.empty_untouched (score.empty_untouched table32 (by decide +kernel)) (by decide +kernel)
    · exact root.optional_hole_untouched hole41 (by decide +kernel)
  exact older

theorem pair_right_older_masks (fuel budget : Nat)
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
    PairOlderMasks after := by
  have older := pair_root_older_masks fuel budget valid callersValid wellFormed typed common setup head tail score root
  have atLeft := older.through_prefix left (List.all_eq_true.mp (by decide +kernel))
  exact atLeft.through_prefix right (List.all_eq_true.mp (by decide +kernel))

theorem PairOlderMasks.through_finish_56 {callee : Derived.Callees} {callers : List Activation}
    {world final : World} {active after : Activation}
    (masks : PairOlderMasks active)
    (steps : Calling.Prefix callee callers (finishCode 56) (finishActions.take 56) world active final after) :
    PairOlderMasks after :=
  masks.through_prefix steps (List.all_eq_true.mp (by decide +kernel))

end SubtreeProofs.Rust.SourceEval.Evaluator
