module

public import SubtreeProofs.Rust.SourceEvalLegacyActions

/-! Successful executions in the earlier helper profile embed exactly in the
expanded evaluator profile, with the entire old cost preserved. The numeric
input premise and recursive callee contract are explicit. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Legacy

open LookupSource LookupSource.Partial

def codeMap {F : Type} (functionMap : F → SourceEval.Function) : Control.Block F → SourceEval.Code
  | .done => .done
  | .ret => .ret
  | .step act rest => .step (actionMap functionMap act) (codeMap functionMap rest)
  | .switch scrut cases fallback left right rest => .switch scrut cases fallback
      (codeMap functionMap left) (codeMap functionMap right) (codeMap functionMap rest)

def outcomeMap : LookupSource.Outcome → SourceEval.Outcome
  | .next env => .next (Locals.lift env)
  | .returned value => .returned value

def OutcomeBounded : LookupSource.Outcome → Prop
  | .next env => EnvBounded env
  | .returned value => Bounded value

def ResultRefines (old : Option (LookupSource.Outcome × LookupSource.Cost))
    (new : Option (SourceEval.Outcome × SourceEval.Cost)) : Prop :=
  ∀ outcome cost, old = some (outcome, cost) →
    new = some (outcomeMap outcome, costMap cost) ∧ OutcomeBounded outcome

theorem selectSource_refines (actual : Key) (cases : List (Key × Nat)) (fallback : Option Nat)
    {left right : Option (LookupSource.Outcome × LookupSource.Cost)}
    {left' right' : Option (SourceEval.Outcome × SourceEval.Cost)}
    (hl : ResultRefines left left') (hr : ResultRefines right right') :
    ResultRefines (Control.selectSource actual cases fallback (fun _ => left) (fun _ => right))
      (Control.selectSource actual cases fallback (fun _ => left') (fun _ => right')) := by
  intro outcome cost he
  simp only [Control.selectSource] at he ⊢
  cases hi : Control.selectIndex actual cases fallback with
  | none => simp [hi] at he
  | some index =>
    cases index with
    | zero => exact hl outcome cost (by simpa only [hi, bind, Option.bind] using he)
    | succ index => cases index with
      | zero => exact hr outcome cost (by simpa only [hi, bind, Option.bind] using he)
      | succ _ => simp [hi] at he

theorem exec_switch (call : Calls) (scrut : LookupSource.Scrutinee) (cases : List (Key × Nat))
    (fallback : Option Nat) (left right rest : SourceEval.Code) (state : State) :
    SourceEval.exec call (.switch scrut cases fallback left right rest) state = (do
      let (actual, state) ← SourceEval.scrutinee state scrut
      let (result, first) ← Control.selectSource actual cases fallback
        (fun _ => SourceEval.exec call left state) (fun _ => SourceEval.exec call right state)
      let charged := (Cost.local (1 + scrut.weight)).plus first
      match result with
      | .returned value => some (.returned value, charged)
      | .next next =>
        let (result, last) ← SourceEval.exec call rest next
        some (result, charged.plus last)) := by
  simp only [SourceEval.exec, Control.execWith]
  cases hs : SourceEval.scrutinee state scrut with
  | none => rfl
  | some pair =>
    rcases pair with ⟨actual, state⟩
    simp only [bind, Option.bind]
    cases hb : Control.selectSource actual cases fallback _ _ with
    | none => rfl
    | some pair => rcases pair with ⟨result, first⟩; cases result <;> rfl

theorem exec_refines {F : Type} {functionMap : F → SourceEval.Function}
    {oldCall : CalleesFor F} {newCall : Calls} (hc : CallsRefine functionMap oldCall newCall)
    (code : Control.Block F) {env : Env} (hb : EnvBounded env) :
    ResultRefines (Control.exec oldCall code env)
      (SourceEval.exec newCall (codeMap functionMap code) (Locals.lift env)) := by
  induction code generalizing env with
  | done => intro outcome cost he; cases he; exact ⟨rfl, hb⟩
  | ret =>
    intro outcome cost he
    simp only [Control.exec_ret, Control.returnValue] at he
    cases hv : env 0 with
    | none => simp [hv] at he
    | some value =>
      simp only [hv, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨by simp only [codeMap, SourceEval.exec_ret, SourceEval.returnValue,
        Locals.lift_materialize, hv, bind, Option.bind]; rfl, hb 0 value hv⟩
  | step act rest ih =>
    intro outcome cost he
    rw [Control.exec_step] at he
    cases ha : act.exec oldCall env with
    | none => simp [ha] at he
    | some pair =>
      rcases pair with ⟨middle, first⟩
      cases hr : Control.exec oldCall rest middle with
      | none => simp [ha, hr] at he
      | some pair =>
        rcases pair with ⟨result, last⟩
        simp only [ha, hr, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨ham, hm⟩ := action_refines hc hb act ha
        obtain ⟨hrm, hout⟩ := ih hm result last hr
        exact ⟨by simp only [codeMap, SourceEval.exec_step, ham, hrm, bind, Option.bind, costMap_plus], hout⟩
  | switch scrut cases fallback left right rest ihLeft ihRight ihRest =>
    intro outcome cost he
    rw [Control.exec_switch] at he
    cases hs : evalScrutinee env scrut with
    | none => simp [hs] at he
    | some pair =>
      rcases pair with ⟨actual, middle⟩
      obtain ⟨hsm, hm⟩ := scrutinee_refines hb scrut hs
      cases ha : Control.selectSource actual cases fallback
        (fun _ => Control.exec oldCall left middle) (fun _ => Control.exec oldCall right middle) with
      | none => simp [hs, ha] at he
      | some pair =>
        rcases pair with ⟨branch, first⟩
        obtain ⟨ham, hbranch⟩ := selectSource_refines actual cases fallback (ihLeft hm) (ihRight hm) branch first ha
        simp only [hs, ha, bind, Option.bind] at he
        simp only [codeMap, exec_switch, hsm, ham, bind, Option.bind]
        cases branch with
        | returned value =>
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact ⟨by rw [costMap_plus, costMap_local]; rfl, hbranch⟩
        | next next =>
          cases hr : Control.exec oldCall rest next with
          | none => simp [hr] at he
          | some pair =>
            rcases pair with ⟨result, last⟩
            simp only [hr, Option.some.injEq, Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            obtain ⟨hrm, hout⟩ := ihRest hbranch result last hr
            exact ⟨by simp only [outcomeMap, hrm, costMap_plus, costMap_local], hout⟩

end SubtreeProofs.Rust.SourceEval.Legacy
