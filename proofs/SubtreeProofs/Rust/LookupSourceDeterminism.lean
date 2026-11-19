module

public import SubtreeProofs.Rust.LookupSource

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource

/-- Replacing callees by extensions preserves every completed action, including
its exact cost. This never identifies value-only equivalent callees. -/
theorem action_extends (first second : Callees)
    (hc : ∀ function args value cost, first function args = some (value, cost) →
      second function args = some (value, cost))
    {action : Action} {env next : Env} {cost : Cost}
    (hr : evalAction first env action = some (next, cost)) :
    evalAction second env action = some (next, cost) := by
  cases action with
  | scope _ => exact hr
  | assign _ _ => exact hr
  | dropMoved _ => exact hr
  | call function args slot =>
    simp only [evalAction, bind, Option.bind_eq_some_iff] at hr ⊢
    obtain ⟨⟨values, state⟩, he, ⟨⟨value, inner⟩, hf, result⟩⟩ := hr
    exact ⟨_, he, _, hc function values value inner hf, result⟩

theorem exec_extends (first second : Callees)
    (hc : ∀ function args value cost, first function args = some (value, cost) →
      second function args = some (value, cost))
    {code : Code} {env : Env} {outcome : Outcome} {cost : Cost}
    (hr : exec first code env = some (outcome, cost)) :
    exec second code env = some (outcome, cost) := by
  induction code generalizing env outcome cost with
  | done => exact hr
  | ret => exact hr
  | step action rest ih =>
    simp only [exec, bind, Option.bind_eq_some_iff] at hr ⊢
    obtain ⟨⟨state, current⟩, ha, ⟨⟨result, last⟩, he, final⟩⟩ := hr
    exact ⟨_, action_extends first second hc ha, _, ih he, final⟩
  | branch scrutinee key other yes no rest ihYes ihNo ihRest =>
    simp only [exec, bind, Option.bind_eq_some_iff] at hr ⊢
    obtain ⟨⟨actual, state⟩, hs, ⟨⟨result, current⟩, ha, final⟩⟩ := hr
    have choice : selectBranch actual key other (fun _ => exec second yes state)
        (fun _ => exec second no state) = some (result, current) := by
      unfold selectBranch at ha ⊢
      split at ha
      · rename_i h
        rw [ite_eq_left h]
        exact ihYes ha
      · rename_i h
        rw [ite_eq_right h]
        split at ha
        · rename_i h
          rw [ite_eq_left h]
          exact ihNo ha
        · cases ha
    refine ⟨_, hs, _, choice, ?_⟩
    cases result with
    | returned value => exact final
    | next state =>
      simp only [Option.bind_eq_some_iff] at final ⊢
      obtain ⟨⟨result, last⟩, he, final⟩ := final
      exact ⟨_, ihRest he, final⟩

/-- Fuel is an evaluator bound, not execution cost. Increasing it cannot change
the value or cost of any completed run. -/
theorem run_extends (body : Function → Code) {small large : Nat} (hf : small ≤ large)
    {function : Function} {args : List Value} {value : Value} {cost : Cost}
    (hr : run body small function args = some (value, cost)) :
    run body large function args = some (value, cost) := by
  induction small generalizing large function args value cost with
  | zero => simp [run] at hr
  | succ small ih =>
    cases large with
    | zero => omega
    | succ large =>
      rw [run_succ] at hr ⊢
      by_cases hb : function = .boxNew
      · simpa only [ite_eq_left hb] using hr
      · rw [ite_eq_right hb] at hr ⊢
        cases he : exec (run body small) (body function) (initialEnv args) with
        | none => simp [he, bind] at hr
        | some pair =>
          have hl := exec_extends (run body small) (run body large)
            (fun _ _ _ _ h => ih (by omega) h) he
          rw [hl]
          simpa only [he] using hr

theorem run_unique (body : Function → Code) {fuel₁ fuel₂ : Nat} {function : Function}
    {args : List Value} {value₁ value₂ : Value} {cost₁ cost₂ : Cost}
    (h₁ : run body fuel₁ function args = some (value₁, cost₁))
    (h₂ : run body fuel₂ function args = some (value₂, cost₂)) :
    value₁ = value₂ ∧ cost₁ = cost₂ := by
  have ha := run_extends body (Nat.le_max_left fuel₁ fuel₂) h₁
  have hb := run_extends body (Nat.le_max_right fuel₁ fuel₂) h₂
  exact Prod.mk.inj (Option.some.inj (ha.symm.trans hb))

end SubtreeProofs.Rust.LookupSource
