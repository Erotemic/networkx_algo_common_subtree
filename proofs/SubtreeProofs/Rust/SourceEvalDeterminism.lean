module

public import SubtreeProofs.Rust.SourceControlExtension
public import SubtreeProofs.Rust.SourceEvalMachine

/-! Nesting fuel is independent of execution cost. More fuel preserves every
completed expanded-profile run, including all work, destruction and call counts. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval

open LookupSource

def CallsExtend (first second : Calls) : Prop :=
  ∀ function args value cost, first function args = some (value, cost) → second function args = some (value, cost)

theorem action_extends (first second : Calls) (hc : CallsExtend first second)
    {instruction : Action} {state after : State} {cost : Cost}
    (hr : action first state instruction = some (after, cost)) :
    action second state instruction = some (after, cost) := by
  cases instruction with
  | storageLive _ | storageDead _ | assign _ _ | drop _ | fakeRead _ | undefinedBehavior => exact hr
  | call function args slot =>
    simp only [action, bind, Option.bind_eq_some_iff] at hr ⊢
    obtain ⟨⟨values, middle⟩, he, ⟨⟨value, inner⟩, hf, final⟩⟩ := hr
    exact ⟨_, he, _, hc function values value inner hf, final⟩

theorem exec_extends (first second : Calls) (hc : CallsExtend first second)
    {code : Code} {state : State} {outcome : Outcome} {cost : Cost}
    (hr : exec first code state = some (outcome, cost)) : exec second code state = some (outcome, cost) :=
  Control.execWith_extends (action first) (action second)
    (fun _ _ pair hp => by rcases pair with ⟨next, cost⟩; exact action_extends first second hc hp)
    scrutinee returnValue Outcome.next nextState {} Cost.plus (fun scrut => Cost.local (1 + scrut.weight)) code hr

theorem run_extends (body : Function → Code) {small large : Nat} (hf : small ≤ large)
    {function : Function} {args : List Value} {value : Value} {cost : Cost}
    (hr : run body small function args = some (value, cost)) :
    run body large function args = some (value, cost) := by
  induction small generalizing large function args value cost with
  | zero => cases hr
  | succ small ih =>
    cases large with
    | zero => omega
    | succ large =>
      have hc : CallsExtend (run body small) (run body large) := fun _ _ _ _ hs => ih (by omega) hs
      cases function with
      | boxNew =>
        cases args with
        | nil => exact hr
        | cons first rest => cases rest <;> exact hr
      | checkedAdd =>
        cases args with
        | nil => exact hr
        | cons first rest => cases rest with
          | nil => cases first <;> exact hr
          | cons last rest => cases rest with
            | nil => cases first <;> cases last <;> exact hr
            | cons _ _ => cases first <;> cases last <;> exact hr
      | copyWord | compare | copyResult | lookup | concatenate | insert | chooseLonger | evaluate | maximum =>
        simp only [run, bind, Option.bind_eq_some_iff] at hr ⊢
        obtain ⟨⟨result, work⟩, he, final⟩ := hr
        exact ⟨_, exec_extends _ _ hc he, final⟩

theorem run_unique (body : Function → Code) {first last : Nat} {function : Function} {args : List Value}
    {value₁ value₂ : Value} {cost₁ cost₂ : Cost}
    (h₁ : run body first function args = some (value₁, cost₁))
    (h₂ : run body last function args = some (value₂, cost₂)) : value₁ = value₂ ∧ cost₁ = cost₂ := by
  have ha := run_extends body (Nat.le_max_left first last) h₁
  have hb := run_extends body (Nat.le_max_right first last) h₂
  rw [ha] at hb
  exact Prod.mk.inj (Option.some.inj hb)

end SubtreeProofs.Rust.SourceEval
