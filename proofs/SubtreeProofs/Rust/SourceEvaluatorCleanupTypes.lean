module

public import SubtreeProofs.Rust.SourceEvaluatorPrefixConstraints

/-! Older cleanup local types follow from certified evaluator call outputs and
their actual field moves. No duplicate parsed-local layout is supplied. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Types

open LookupSource Heap

theorem evaluator_result_optional_type {locals : List Ty} {args : List Operand} {packet destination : Nat}
    (call : ActionConstraints locals (.call .evaluate args packet))
    (move : ActionConstraints locals (.assign destination (.use (.move (.field (.local packet) none 0))))) :
    locals[destination]? = some (.adt .optional) := by
  obtain ⟨types, ty, arguments, output, packetType⟩ := call
  simp only [callOutput] at output
  split at output
  next impossible => cases impossible
  next other =>
    split at output
    next same =>
      cases output
      obtain ⟨result, destinationType, expression⟩ := move
      cases expression with
      | use inferred =>
        simp only [inferOperand, inferMovePlace, packetType, Types.output, bind, Option.bind,
          SourceTypes.fieldType, List.getElem?_cons_zero, Option.some.injEq] at inferred
        cases inferred
        exact destinationType
    next => cases output

end SubtreeProofs.Rust.SourceEval.Types

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap

theorem evaluator_cleanup_optional_types :
    CallingCertificate.originalEvaluator.locals[31]? = some (.adt .optional) ∧
    CallingCertificate.originalEvaluator.locals[41]? = some (.adt .optional) := by
  constructor
  · exact Types.evaluator_result_optional_type (packet := 33)
      (args := [.move (.local 34), .move (.local 35), .move (.local 36)])
      (evaluator_prefix_constraints.heads _ (by simp [headActions]))
      (evaluator_prefix_constraints.heads _ (by simp [headActions]))
  · exact Types.evaluator_result_optional_type (packet := 43)
      (args := [.move (.local 44), .move (.local 45), .move (.local 46)])
      (evaluator_prefix_constraints.tails _ (by simp [tailActions]))
      (evaluator_prefix_constraints.tails _ (by simp [tailActions]))

end SubtreeProofs.Rust.SourceEval.Evaluator
