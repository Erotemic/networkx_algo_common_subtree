module

public import SubtreeProofs.Rust.SourceCallingReturnedRouting
public import SubtreeProofs.Rust.SourcePairRouteInspections
public import SubtreeProofs.Rust.SourcePairFinishComplete

/-! Compose the eight actual prefixes, successful inspections and constructed
finish return through every retained switch of the original parent body. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_successful_body_routing (callee : Derived.Callees)
    {entered lookupWorld missWorld headWorld tailWorld scoreWorld rootWorld leftWorld rightWorld final : World}
    {active lookupActive missActive headActive tailActive scoreActive rootActive leftActive rightActive after : Activation}
    {callers : List Activation} {packet : ValueCell} {finishCost : Cost}
    (common : Calling.Prefix callee callers lookupSwitch commonPrefix entered active lookupWorld lookupActive)
    (setup : Calling.Prefix callee callers missCases missSetupActions lookupWorld lookupActive missWorld missActive)
    (head : Calling.Prefix callee callers headCases headActions missWorld missActive headWorld headActive)
    (tail : Calling.Prefix callee callers tailCases tailActions headWorld headActive tailWorld tailActive)
    (score : Calling.Prefix callee callers scoreCases scoreActions tailWorld tailActive scoreWorld scoreActive)
    (root : Calling.Prefix callee callers rootScoreCases rootScoreActions scoreWorld scoreActive rootWorld rootActive)
    (left : Calling.Prefix callee callers matchedCases matchedActions rootWorld rootActive leftWorld leftActive)
    (right : Calling.Prefix callee callers rightContractionCases rightActions leftWorld leftActive rightWorld rightActive)
    (lookupInspect : Derived.scrutinee lookupWorld lookupActive callers (.discriminant (.local 4)) = some (.variant .optional 0, lookupActive))
    (queryLeft : Derived.scrutinee missWorld missActive callers (.discriminant (.deref (.field (.local 13) none 0))) = some (.variant .word 1, missActive))
    (queryRight : Derived.scrutinee missWorld missActive callers (.discriminant (.deref (.field (.local 13) none 1))) = some (.variant .word 1, missActive))
    (headInspect : Derived.scrutinee headWorld headActive callers (.discriminant (.local 31)) = some (.variant .optional 1, headActive))
    (tailInspect : Derived.scrutinee tailWorld tailActive callers (.discriminant (.local 41)) = some (.variant .optional 1, tailActive))
    (scoreInspect : Derived.scrutinee scoreWorld scoreActive callers (.discriminant (.local 52)) = some (.variant .optional 1, scoreActive))
    (rootInspect : Derived.scrutinee rootWorld rootActive callers (.discriminant (.local 59)) = some (.variant .optional 1, rootActive))
    (leftInspect : Derived.scrutinee leftWorld leftActive callers (.discriminant (.local 74)) = some (.variant .optional 1, leftActive))
    (rightInspect : Derived.scrutinee rightWorld rightActive callers (.discriminant (.local 88)) = some (.variant .optional 1, rightActive))
    (finishRun : Calling.exec callee callers finish rightWorld rightActive = some (.returned final after packet, finishCost)) :
    ∃ cost, Calling.exec callee callers body entered active = some (.returned final after packet, cost) := by
  have rightCasesRun : Calling.exec callee callers rightContractionCases rightWorld rightActive =
      some (.returned final after packet, _) :=
    Calling.exec_switch_right_returned rightInspect (by rfl) finishRun
  obtain ⟨rightCost, rightRun⟩ := right.exec rightCasesRun
  have contractRightRun : Calling.exec callee callers contractRight leftWorld leftActive = some (.returned final after packet, rightCost) := by
    rw [contractRight_actions]; exact rightRun
  have leftCasesRun : Calling.exec callee callers matchedCases leftWorld leftActive = some (.returned final after packet, _) :=
    Calling.exec_switch_right_returned leftInspect (by rfl) contractRightRun
  obtain ⟨leftCost, leftRun⟩ := left.exec leftCasesRun
  have contractLeftRun : Calling.exec callee callers contractLeft rootWorld rootActive = some (.returned final after packet, leftCost) := by
    rw [contractLeft_actions]; exact leftRun
  have rootCasesRun : Calling.exec callee callers rootScoreCases rootWorld rootActive = some (.returned final after packet, _) :=
    Calling.exec_switch_right_returned rootInspect (by rfl) contractLeftRun
  obtain ⟨rootCost, rootRun⟩ := root.exec rootCasesRun
  have addRootRun : Calling.exec callee callers addRoot scoreWorld scoreActive = some (.returned final after packet, rootCost) := by
    rw [addRoot_actions]; exact rootRun
  have scoreCasesRun : Calling.exec callee callers scoreCases scoreWorld scoreActive = some (.returned final after packet, _) :=
    Calling.exec_switch_right_returned scoreInspect (by rfl) addRootRun
  obtain ⟨scoreCost, scoreRun⟩ := score.exec scoreCasesRun
  have addScoresRun : Calling.exec callee callers addScores tailWorld tailActive = some (.returned final after packet, scoreCost) := by
    rw [addScores_actions]; exact scoreRun
  have tailCasesRun : Calling.exec callee callers tailCases tailWorld tailActive = some (.returned final after packet, _) :=
    Calling.exec_switch_right_returned tailInspect (by rfl) addScoresRun
  obtain ⟨tailCost, tailRun⟩ := tail.exec tailCasesRun
  have recurseTailsRun : Calling.exec callee callers recurseTails headWorld headActive = some (.returned final after packet, tailCost) := by
    rw [recurseTails_actions]; exact tailRun
  have headCasesRun : Calling.exec callee callers headCases headWorld headActive = some (.returned final after packet, _) :=
    Calling.exec_switch_right_returned headInspect (by rfl) recurseTailsRun
  obtain ⟨headCost, headRun⟩ := head.exec headCasesRun
  have recurseHeadsRun : Calling.exec callee callers recurseHeads missWorld missActive = some (.returned final after packet, headCost) := by
    rw [recurseHeads_actions]; exact headRun
  let pairCost := ((Cost.local (1 + (Scrutinee.discriminant (.deref (.field (.local 13) none 0))).weight)).plus {}).plus headCost
  have pairRun : Calling.exec callee callers leftPairCheck missWorld missActive = some (.returned final after packet, pairCost) := by
    rw [leftPairCheck, Calling.exec_switch, queryLeft]
    simp only [Control.selectSource, Control.selectIndex, ite_true, Calling.exec_done, bind, Option.bind, recurseHeadsRun]
    rfl
  have rightWordRun : Calling.exec callee callers rightCases missWorld missActive = some (.returned final after packet, _) :=
    Calling.exec_switch_right_returned queryRight (by rfl) pairRun
  have wordCasesRun : Calling.exec callee callers missCases missWorld missActive = some (.returned final after packet, _) :=
    Calling.exec_switch_right_returned queryLeft (by rfl) rightWordRun
  obtain ⟨missCost, missRun⟩ := setup.exec wordCasesRun
  have cacheMissRun : Calling.exec callee callers cacheMiss lookupWorld lookupActive = some (.returned final after packet, missCost) := by
    rw [cacheMiss_actions]; exact missRun
  have lookupRun : Calling.exec callee callers lookupSwitch lookupWorld lookupActive = some (.returned final after packet, _) :=
    Calling.exec_switch_right_returned lookupInspect (by rfl) cacheMissRun
  obtain ⟨cost, whole⟩ := common.exec lookupRun
  refine ⟨cost, ?_⟩
  rw [← actual_body, actual_body_common_prefix]
  exact whole

end SubtreeProofs.Rust.SourceEval.Evaluator
