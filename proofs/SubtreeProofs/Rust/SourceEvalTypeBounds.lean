module

public import SubtreeProofs.Rust.SourceEvalTypeCalls
public import SubtreeProofs.Rust.SourceActivationLoanViews

/-! Existing source types imply the scalar-width domain of the legacy helper
embedding. Ending certified unused reference views also preserves these same
partial-local types; holes retain their original declared type. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap

mutual
  theorem SnapshotTyped.bounded {value : Value} {ty : Ty} (h : SnapshotTyped value ty) :
      SourceEval.Legacy.Bounded value :=
    match h with
    | .boolean b => .boolean b
    | .number bound => .number bound
    | .node _ fields => .node (SnapshotFieldsTyped.bounded fields)
    | .shared inner => .reference (SnapshotTyped.bounded inner)
    | .owned inner => .boxed (SnapshotTyped.bounded inner)

  theorem SnapshotFieldsTyped.bounded {values : List Value} {types : List Ty} (h : SnapshotFieldsTyped values types) :
      SourceEval.Legacy.FieldsBounded values :=
    match h with
    | .nil => .nil
    | .cons first rest => .cons (SnapshotTyped.bounded first) (SnapshotFieldsTyped.bounded rest)
end

end SubtreeProofs.Rust.LookupSource.Heap

namespace SubtreeProofs.Rust.LookupSource.Partial

open Heap

theorem LocalsTyped.forget {locals : List Ty} {state : Locals} (h : LocalsTyped locals state)
    (code : SourceEval.Code) (slots : List Nat) : LocalsTyped locals (SourceEval.LoanEnding.forget code slots state) := by
  induction slots generalizing state with
  | nil => exact h
  | cons slot rest ih =>
    simp only [SourceEval.LoanEnding.forget_cons]
    cases hs : state slot <;> try exact ih h
    by_cases he : SourceEval.LoanEnding.endsBeforeObservation slot code = true
    · simp only [he, ite_true]
      exact ih (h.clear slot)
    · simp only [he, Bool.false_eq_true, ite_false]
      exact ih h

end SubtreeProofs.Rust.LookupSource.Partial

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open Heap

theorem Activation.forgetRefs_typed {active : Activation} {locals : List Ty}
    (h : LocalsTyped locals active.state) (code : SourceEval.Code) :
    LocalsTyped locals (active.forgetRefs code).state := h.forget code _

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage
