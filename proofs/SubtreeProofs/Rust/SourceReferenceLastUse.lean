module

public import SubtreeProofs.Rust.SourceCallingPrefixes

/-! A listed shared local is empty after the existing preparation proves its
last observation has ended. This states the effect of the actual finite scan,
including repeated indices, rather than changing its lifetime analysis. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.LoanEnding

open LookupSource Partial

theorem forget_ended_shared (code : Code) (slots : List Nat) {state : State} {index : Nat} {value : Value}
    (member : index ∈ slots) (shared : state index = .shared value)
    (ended : endsBeforeObservation index code = true) : forget code slots state index = .empty := by
  induction slots generalizing state with
  | nil => cases member
  | cons slot rest ih =>
    rw [forget_cons]
    by_cases same : index = slot
    · subst slot
      simp only [shared, ended, ite_true]
      apply forget_empty
      simp only [Locals.set, ite_true]
    · have tail : index ∈ rest := (List.mem_cons.mp member).resolve_left same
      cases current : state slot <;> try exact ih tail shared
      by_cases otherEnded : endsBeforeObservation slot code = true
      · simp only [otherEnded, ite_true]
        apply ih tail
        simpa only [Locals.set, same, ite_false] using shared
      · simpa only [otherEnded, Bool.false_eq_true, ite_false] using ih tail shared

end SubtreeProofs.Rust.SourceEval.LoanEnding
