module

public import SubtreeProofs.Rust.SourceOptionalPayloadTag
public import SubtreeProofs.Rust.SourceEvaluatorRouteTypes
public import SubtreeProofs.Rust.SourcePairReturnStorage

/-! Construct earlier successful optional inspections from the payload reads
in already constructed finite prefixes. No whole-parent path is assumed. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_successful_route_inspections (fuel budget : Nat)
    {entered lookupWorld missWorld headWorld tailWorld scoreWorld rootWorld leftWorld : World}
    {active lookupActive missActive headActive tailActive scoreActive rootActive leftActive : Activation}
    {callers : List Activation}
    (valid : active.Valid entered) (callersValid : ∀ caller ∈ callers, caller.Valid entered) (wellFormed : entered.WellFormed)
    (typed : LocalsTyped CallingCertificate.originalEvaluator.locals active.state)
    (common : Calling.Prefix (Recursive.original budget fuel) callers lookupSwitch commonPrefix entered active lookupWorld lookupActive)
    (setup : Calling.Prefix (Recursive.original budget fuel) callers missCases missSetupActions lookupWorld lookupActive missWorld missActive)
    (head : Calling.Prefix (Recursive.original budget fuel) callers headCases headActions missWorld missActive headWorld headActive)
    (tail : Calling.Prefix (Recursive.original budget fuel) callers tailCases tailActions headWorld headActive tailWorld tailActive)
    (score : Calling.Prefix (Recursive.original budget fuel) callers scoreCases scoreActions tailWorld tailActive scoreWorld scoreActive)
    (root : Calling.Prefix (Recursive.original budget fuel) callers rootScoreCases rootScoreActions scoreWorld scoreActive rootWorld rootActive)
    (left : Calling.Prefix (Recursive.original budget fuel) callers matchedCases matchedActions rootWorld rootActive leftWorld leftActive) :
    Derived.scrutinee headWorld headActive callers (.discriminant (.local 31)) = some (.variant .optional 1, headActive) ∧
    Derived.scrutinee tailWorld tailActive callers (.discriminant (.local 41)) = some (.variant .optional 1, tailActive) ∧
    Derived.scrutinee scoreWorld scoreActive callers (.discriminant (.local 52)) = some (.variant .optional 1, scoreActive) ∧
    Derived.scrutinee rootWorld rootActive callers (.discriminant (.local 59)) = some (.variant .optional 1, rootActive) := by
  have respects := Recursive.original_typed_respects budget fuel
  have sourceTyped := Types.original_run_typed fuel
  have constraints := evaluator_prefix_constraints
  have c0 := common.typed_spec respects sourceTyped valid callersValid wellFormed typed constraints.common
  have c1 := setup.typed_spec respects sourceTyped c0.1 c0.2.1 c0.2.2.1 c0.2.2.2 constraints.miss
  have c2 := head.typed_spec respects sourceTyped c1.1 c1.2.1 c1.2.2.1 c1.2.2.2 constraints.heads
  have c3 := tail.typed_spec respects sourceTyped c2.1 c2.2.1 c2.2.2.1 c2.2.2.2 constraints.tails
  have c4 := score.typed_spec respects sourceTyped c3.1 c3.2.1 c3.2.2.1 c3.2.2.2 constraints.scores
  have c5 := root.typed_spec respects sourceTyped c4.1 c4.2.1 c4.2.2.1 c4.2.2.2 constraints.roots
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Calling.Prefix.typed_payload_tag respects sourceTyped
      (before := tailActions.take 1) (rest := tailActions.drop 2) (slot := 31) (destination := 38)
      (op := .move (.field (.local 31) (some 1) 0)) tail c2.1 c2.2.1 c2.2.2.1 c2.2.2.2
      (fun act member => constraints.tails act (List.mem_of_mem_take member)) evaluator_cleanup_optional_types.1
      (Or.inl rfl) (.adt .optional) (by decide +kernel)
      (by intro state value remaining run; simp only [SourceEval.operand] at run; exact (Partial.Locals.move_spec run).1)
  · exact Calling.Prefix.typed_payload_tag respects sourceTyped
      (before := scoreActions.take 1) (rest := scoreActions.drop 2) (slot := 41) (destination := 48)
      (op := .move (.field (.local 41) (some 1) 0)) score c3.1 c3.2.1 c3.2.2.1 c3.2.2.2
      (fun act member => constraints.scores act (List.mem_of_mem_take member)) evaluator_cleanup_optional_types.2
      (Or.inl rfl) (.adt .optional) (by decide +kernel)
      (by intro state value remaining run; simp only [SourceEval.operand] at run; exact (Partial.Locals.move_spec run).1)
  · exact Calling.Prefix.typed_payload_tag respects sourceTyped
      (before := rootScoreActions.take 1) (rest := rootScoreActions.drop 2) (slot := 52) (destination := 55)
      (op := .copy (.field (.local 52) (some 1) 0)) root c4.1 c4.2.1 c4.2.2.1 c4.2.2.2
      (fun act member => constraints.roots act (List.mem_of_mem_take member)) evaluator_score_option_types.1
      (Or.inr ⟨.u32, rfl⟩) (.option .u32) (by decide +kernel)
      (by intro state value remaining run; exact (copy_nonowning run).2.1)
  · exact Calling.Prefix.typed_payload_tag respects sourceTyped
      (before := matchedActions.take 1) (rest := matchedActions.drop 2) (slot := 59) (destination := 61)
      (op := .copy (.field (.local 59) (some 1) 0)) left c5.1 c5.2.1 c5.2.2.1 c5.2.2.2
      (fun act member => constraints.matched act (List.mem_of_mem_take member)) evaluator_score_option_types.2
      (Or.inr ⟨.u32, rfl⟩) (.option .u32) (by decide +kernel)
      (by intro state value remaining run; exact (copy_nonowning run).2.1)

end SubtreeProofs.Rust.SourceEval.Evaluator
