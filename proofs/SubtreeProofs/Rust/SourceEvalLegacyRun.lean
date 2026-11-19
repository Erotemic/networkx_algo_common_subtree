module

public import SubtreeProofs.Rust.SourceEvalLegacyControl

/-! A compatibility theorem for existing recursive helper drivers. The driver
record requires their actual zero/successor equations; it does not introduce a
second interpreter. The expanded profile preserves all successful old runs at
identical call-nesting fuel and full declared cost. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Legacy

open LookupSource LookupSource.Partial

structure Driver (F : Type) [DecidableEq F] where
  body : F → Control.Block F
  box : F
  entry : F → LookupEvents.Events
  run : Nat → CalleesFor F
  zero : ∀ function args, run 0 function args = none
  succ : ∀ fuel function args, run (fuel + 1) function args =
    (if function = box then
      match args with
      | [value] => some (.boxed value, ⟨1, entry function⟩)
      | _ => none
    else do
      let (outcome, cost) ← Control.exec (run fuel) (body function) (initialEnv args)
      match outcome with
      | .next _ => none
      | .returned value => some (value, (⟨1, entry function⟩ : LookupSource.Cost).plus cost))

theorem initialEnv_bounded {args : List Value} (h : FieldsBounded args) : EnvBounded (initialEnv args) := by
  intro slot value hv
  unfold initialEnv at hv
  split at hv
  · cases hv
  · exact h.get (slot - 1) hv

theorem run_ordinary (body : SourceEval.Function → SourceEval.Code) (fuel : Nat)
    (function : SourceEval.Function) (args : List Value)
    (hb : function ≠ .boxNew) (ha : function ≠ .checkedAdd) :
    SourceEval.run body (fuel + 1) function args = (do
      let (result, work) ← SourceEval.exec (SourceEval.run body fuel) (body function) (initialState args)
      match result with
      | .next _ => none
      | .returned value => some (value, (Cost.entry function).plus work)) := by
  cases function <;> first | rfl | contradiction

theorem run_refines {F : Type} [DecidableEq F] (driver : Driver F)
    (functionMap : F → SourceEval.Function) (hinj : Function.Injective functionMap)
    (hbox : functionMap driver.box = .boxNew)
    (hadd : ∀ function, functionMap function ≠ .checkedAdd)
    (hentry : ∀ function, Cost.entry (functionMap function) = costMap ⟨1, driver.entry function⟩)
    (body : SourceEval.Function → SourceEval.Code)
    (hbody : ∀ function, body (functionMap function) = codeMap functionMap (driver.body function))
    (fuel : Nat) : CallsRefine functionMap (driver.run fuel) (SourceEval.run body fuel) := by
  induction fuel with
  | zero => intro function args value cost _ hr; rw [driver.zero] at hr; cases hr
  | succ fuel ih =>
    intro function args value cost hb hr
    rw [driver.succ] at hr
    by_cases hf : function = driver.box
    · subst function
      simp only [ite_true] at hr
      cases hb with
      | nil => cases hr
      | cons first rest =>
        cases rest with
        | cons _ _ => cases hr
        | nil =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          refine ⟨.boxed first, ?_⟩
          have hc := hentry driver.box
          rw [hbox] at hc ⊢
          simp only [SourceEval.run, hc]
    · simp only [hf, ite_false] at hr
      have hn : functionMap function ≠ .boxNew := by
        intro he
        exact hf (hinj (he.trans hbox.symm))
      cases he : Control.exec (driver.run fuel) (driver.body function) (initialEnv args) with
      | none => simp [he] at hr
      | some pair =>
        rcases pair with ⟨result, work⟩
        simp only [he, bind, Option.bind] at hr
        cases result with
        | next _ => cases hr
        | returned output =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          obtain ⟨hm, hv⟩ := exec_refines ih (driver.body function) (initialEnv_bounded hb) _ _ he
          refine ⟨hv, ?_⟩
          rw [run_ordinary body fuel (functionMap function) args hn (hadd function), hbody]
          simp only [initialState, hm, outcomeMap, bind, Option.bind, hentry, costMap_plus]

end SubtreeProofs.Rust.SourceEval.Legacy
