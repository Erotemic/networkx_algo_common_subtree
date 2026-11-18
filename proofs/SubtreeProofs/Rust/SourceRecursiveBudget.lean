module

public import SubtreeProofs.Rust.SourceCallingExtension

/-! Increasing call fuel and ghost readback budgets preserves completed actual
recursive executions, including all caller worlds, packets and full costs.
The original program and arbitrary parsed-program dispatch use the same law. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Recursive

open LookupSource Heap Partial Partial.Addressed Storage

theorem run_budget_enlarge (program : List TypeReader.Definition) (fuel : Nat)
    {small large : Nat} (bound : small ≤ large) :
    Derived.CallsExtend (run program small fuel) (run program large fuel) := by
  induction fuel with
  | zero => intro world guards callers function packets final packet cost h; cases h
  | succ fuel ih =>
    intro world guards callers function packets final packet cost h
    by_cases interpreted : Recursive.interpreted function = true
    · simp only [run, interpreted, ite_true] at h ⊢
      cases hf : program.find? (fun decl => decl.source.function == function) with
      | none => simp [hf] at h
      | some decl =>
        simp only [hf, bind, Option.bind] at h ⊢
        exact Calling.guardedInvoke_extends ih h
    · simp only [run, interpreted] at h ⊢
      exact Helpers.execute_budget_enlarge bound h

theorem original_budget_enlarge {fuel small large : Nat} (bound : small ≤ large)
    {world final : World} {guards : List Nat} {callers : List Activation} {function : Function}
    {packets : List ValueCell} {packet : ValueCell} {cost : Cost}
    (h : original small fuel world guards callers function packets = some (final, packet, cost)) :
    original large fuel world guards callers function packets = some (final, packet, cost) :=
  run_budget_enlarge CallingCertificate.originalProgram.definitions fuel bound _ _ _ _ _ _ _ _ h

theorem run_fuel_enlarge (program : List TypeReader.Definition) (budget : Nat)
    {small large : Nat} (bound : small ≤ large) :
    Derived.CallsExtend (run program budget small) (run program budget large) := by
  induction small generalizing large with
  | zero => intro world guards callers function packets final packet cost h; cases h
  | succ small ih =>
    cases large with
    | zero => omega
    | succ large =>
      intro world guards callers function packets final packet cost h
      by_cases interpreted : Recursive.interpreted function = true
      · simp only [run, interpreted, ite_true] at h ⊢
        cases hf : program.find? (fun decl => decl.source.function == function) with
        | none => simp [hf] at h
        | some decl =>
          simp only [hf, bind, Option.bind] at h ⊢
          exact Calling.guardedInvoke_extends (ih (by omega)) h
      · simp only [run, interpreted] at h ⊢
        exact Helpers.execute_fuel_enlarge (by omega) h

theorem original_fuel_enlarge {budget small large : Nat} (bound : small ≤ large)
    {world final : World} {guards : List Nat} {callers : List Activation} {function : Function}
    {packets : List ValueCell} {packet : ValueCell} {cost : Cost}
    (h : original budget small world guards callers function packets = some (final, packet, cost)) :
    original budget large world guards callers function packets = some (final, packet, cost) :=
  run_fuel_enlarge CallingCertificate.originalProgram.definitions budget bound _ _ _ _ _ _ _ _ h

theorem original_enlarge {smallFuel largeFuel smallBudget largeBudget : Nat}
    (fuelBound : smallFuel ≤ largeFuel) (budgetBound : smallBudget ≤ largeBudget)
    {world final : World} {guards : List Nat} {callers : List Activation} {function : Function}
    {packets : List ValueCell} {packet : ValueCell} {cost : Cost}
    (h : original smallBudget smallFuel world guards callers function packets = some (final, packet, cost)) :
    original largeBudget largeFuel world guards callers function packets = some (final, packet, cost) :=
  original_budget_enlarge budgetBound (original_fuel_enlarge fuelBound h)

end SubtreeProofs.Rust.SourceEval.Addressed.Recursive
