module

public import SubtreeProofs.Rust.SourceEvaluatorCleanupTypes

/-! The checked scalar-option call outputs determine the two score-switch
local types without reproducing the parsed local layout. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Types

open LookupSource Heap

theorem call_result_type {locals : List Ty} {function : Function} {args : List Operand} {destination : Nat}
    (ordinary : function ≠ .boxNew) (call : ActionConstraints locals (.call function args destination)) :
    locals[destination]? = some (output function) := by
  obtain ⟨types, ty, arguments, result, destinationType⟩ := call
  simp only [callOutput, ordinary, ite_false] at result
  split at result
  next same => cases result; exact destinationType
  next => cases result

end SubtreeProofs.Rust.SourceEval.Types

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap

theorem evaluator_score_option_types :
    CallingCertificate.originalEvaluator.locals[52]? = some (.option .u32) ∧
    CallingCertificate.originalEvaluator.locals[59]? = some (.option .u32) := by
  constructor
  · exact Types.call_result_type (function := .checkedAdd) (args := [.move (.local 53), .move (.local 54)]) (by decide)
      (evaluator_prefix_constraints.scores _ (by simp [scoreActions]))
  · exact Types.call_result_type (function := .checkedAdd) (args := [.move (.local 60), .number 1]) (by decide)
      (evaluator_prefix_constraints.roots _ (by simp [rootScoreActions]))

end SubtreeProofs.Rust.SourceEval.Evaluator
