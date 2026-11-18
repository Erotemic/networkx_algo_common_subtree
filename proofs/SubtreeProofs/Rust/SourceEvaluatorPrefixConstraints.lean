module

public import SubtreeProofs.Rust.SourceTypedPrefixes
public import SubtreeProofs.Rust.SourcePairFinishProgram

/-! Read the existing parsed type certificate along the actual evaluator
branches. Every finite action list inherits its constraints from that certificate;
no duplicate local layout or additional source checker is introduced. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed

structure PrefixConstraints (locals : List Ty) : Prop where
  common : ∀ act ∈ commonPrefix, Types.ActionConstraints locals act
  miss : ∀ act ∈ missSetupActions, Types.ActionConstraints locals act
  heads : ∀ act ∈ headActions, Types.ActionConstraints locals act
  tails : ∀ act ∈ tailActions, Types.ActionConstraints locals act
  scores : ∀ act ∈ scoreActions, Types.ActionConstraints locals act
  roots : ∀ act ∈ rootScoreActions, Types.ActionConstraints locals act
  matched : ∀ act ∈ matchedActions, Types.ActionConstraints locals act
  right : ∀ act ∈ rightActions, Types.ActionConstraints locals act
  finish : ∀ act ∈ finishActions, Types.ActionConstraints locals act

theorem evaluator_prefix_constraints : PrefixConstraints CallingCertificate.originalEvaluator.locals := by
  have bodyTypes := CallingCertificate.originalEvaluator.constraints
  rw [CallingCertificate.originalEvaluator_spec.1, CallingCertificate.originalEvaluator_spec.2.2] at bodyTypes
  rw [← actual_body] at bodyTypes
  rw [actual_body_common_prefix] at bodyTypes
  have commonTypes := bodyTypes.prefix
  have missTypes := commonTypes.2.branches.2.1
  rw [cacheMiss_actions] at missTypes
  have missParts := missTypes.prefix
  have rightTypes := missParts.2.branches.2.1
  have leftPairTypes := rightTypes.branches.2.1
  have headTypes := leftPairTypes.branches.2.2
  rw [recurseHeads_actions] at headTypes
  have headParts := headTypes.prefix
  have tailTypes := headParts.2.branches.2.1
  rw [recurseTails_actions] at tailTypes
  have tailParts := tailTypes.prefix
  have scoreTypes := tailParts.2.branches.2.1
  rw [addScores_actions] at scoreTypes
  have scoreParts := scoreTypes.prefix
  have rootTypes := scoreParts.2.branches.2.1
  rw [addRoot_actions] at rootTypes
  have rootParts := rootTypes.prefix
  have matchedTypes := rootParts.2.branches.2.1
  rw [contractLeft_actions] at matchedTypes
  have matchedParts := matchedTypes.prefix
  have contractionTypes := matchedParts.2.branches.2.1
  rw [contractRight_actions] at contractionTypes
  have rightParts := contractionTypes.prefix
  have finishTypes := rightParts.2.branches.2.1
  rw [finish_actions] at finishTypes
  exact ⟨commonTypes.1, missParts.1, headParts.1, tailParts.1, scoreParts.1, rootParts.1, matchedParts.1,
    rightParts.1, finishTypes.prefix.1⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
