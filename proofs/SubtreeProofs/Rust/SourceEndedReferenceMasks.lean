module

public import SubtreeProofs.Rust.SourcePrefixCallPreservation

/-! Actual continuation preparation ends an unobserved shared mask. Once
empty, untouched masks stay empty across actual calls and non-call actions. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.LoanEnding

open LookupSource Partial

theorem forget_shared_ended (code : Code) (slots : List Nat) {state : State} {index : Nat} {value : Value}
    (member : index ∈ slots) (shared : state index = .shared value) (ended : endsBeforeObservation index code = true) :
    forget code slots state index = .empty := by
  induction slots generalizing state with
  | nil => cases member
  | cons slot rest ih =>
    by_cases same : index = slot
    · subst slot
      rw [forget_cons, shared, ended]
      simp only [ite_true]
      exact forget_empty code rest (by simp only [Partial.Locals.set, ite_true])
    · have remaining : index ∈ rest := (List.mem_cons.mp member).resolve_left same
      cases atSlot : state slot <;> simp only [forget_cons, atSlot] <;> try exact ih remaining shared
      by_cases ending : endsBeforeObservation slot code = true
      · simp only [ending, ite_true]
        apply ih remaining
        simpa only [Partial.Locals.set, same, ite_false] using shared
      · simp only [ending, Bool.false_eq_true, ite_false]
        exact ih remaining shared

end SubtreeProofs.Rust.SourceEval.LoanEnding

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource Heap Partial Partial.Addressed Storage

theorem Prefix.ended_shared_local_empty_calls {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {act : Action} {rest : List Action} {world final : World} {active after : Activation}
    (h : Prefix callee callers suffix (act :: rest) world active final after)
    {index : Nat} {value : Value} (bound : index < active.count) (shared : active.state index = .shared value)
    (ended : LoanEnding.endsBeforeObservation index ((act :: rest).foldr Control.Tree.step suffix) = true)
    (unchanged : (act :: rest).all (LocalPreservation.action index) = true) : after.state index = .empty := by
  cases h with
  | @cons world middle final active current after act rest cost run tail =>
    let code := (act :: rest).foldr Control.Tree.step suffix
    have preparedEmpty : (active.forgetRefs code).state index = .empty :=
      LoanEnding.forget_shared_ended code (List.range active.count) (List.mem_range.mpr bound) shared ended
    have all := List.all_eq_true.mp unchanged
    have currentEmpty : current.state index = .empty :=
      (instruction_local_same index (all act (by simp)) run).trans preparedEmpty
    exact (tail.unshared_local_same_calls (index := index) (by rw [currentEmpty]; simp)
      (List.all_eq_true.mpr (fun action member => all action (List.mem_cons_of_mem act member)))).trans currentEmpty

end SubtreeProofs.Rust.SourceEval.Addressed.Calling
