module

public import SubtreeProofs.Rust.SourceEvalTypePrimitives
public import SubtreeProofs.Rust.SourceEvalLegacyValues
public import SubtreeProofs.Rust.SourceControlSpecification

/-! Successful control execution preserves the independent partial-local and
returned snapshot types. Primitive/callee contracts are consumed at their actual
execution points. Initialization, addressed ownership and loans remain separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Types

open LookupSource Heap Partial

theorem operandMap_type (locals : List Ty) (op : LookupSource.Operand) :
    inferOperand locals (Legacy.operandMap op) = SourceTypes.inferOperand locals op := by
  cases op <;> simp only [Legacy.operandMap, inferOperand, inferMovePlace, SourceTypes.inferOperand]

theorem scrutinee_value (state : State) (op : LookupSource.Operand) :
    SourceEval.scrutinee state (.value op) = (do
      let (value, after) ← operand state (Legacy.operandMap op)
      match value with
      | .boolean value => some (.boolean value, after)
      | _ => none) := by
  cases op <;> rfl

theorem scrutinee_typed {locals : List Ty} {state after : State} (he : LocalsTyped locals state)
    (scrut : Scrutinee) {kind : Option Kind} {key : Key}
    (ht : scrutineeType locals scrut = some kind)
    (hr : SourceEval.scrutinee state scrut = some (key, after)) : LocalsTyped locals after := by
  cases scrut with
  | discriminant place =>
    rcases hp : splitPlace place with ⟨slot, path⟩
    simp only [SourceEval.scrutinee, hp] at hr
    cases hg : (state slot).get path with
    | none => simp [hg] at hr
    | some part =>
      simp only [hg, bind, Option.bind] at hr
      cases part <;> try contradiction
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact he
  | value op =>
    simp only [scrutineeType] at ht
    split at ht
    next hc =>
      obtain ⟨ty, ho, hb⟩ := SourceTypes.sameResult_sound hc
      cases hb
      rw [scrutinee_value] at hr
      cases hx : operand state (Legacy.operandMap op) with
      | none => simp [hx] at hr
      | some pair =>
        rcases pair with ⟨value, finalState⟩
        obtain ⟨_, ha⟩ := operand_typed he (Legacy.operandMap op) (by rw [operandMap_type]; exact ho) hx
        simp only [hx, bind, Option.bind] at hr
        cases value <;> try contradiction
        simp only [Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ha
    next => cases ht

def OutcomeTyped (locals : List Ty) (output : Ty) : SourceEval.Outcome → Prop
  | .next state => LocalsTyped locals state
  | .returned value => SnapshotTyped value output

theorem exec_typed {call : Calls} (hcall : CallsTyped call)
    {locals : List Ty} {output : Ty} {state : State} {result : SourceEval.Outcome} {cost : SourceEval.Cost}
    (he : LocalsTyped locals state) {code : SourceEval.Code} (ht : CodeConstraints locals output code)
    (hr : SourceEval.exec call code state = some (result, cost)) : OutcomeTyped locals output result := by
  induction ht generalizing state result cost with
  | done =>
    simp only [SourceEval.exec, Control.execWith, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact he
  | ret hret =>
    simp only [SourceEval.exec_ret, SourceEval.returnValue] at hr
    cases hx : (state 0).materialize with
    | none => simp [hx] at hr
    | some value =>
      simp only [hx, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact (he 0 output hret).materialize hx
  | @step instruction rest ha ht ih =>
    simp only [SourceEval.exec_step, bind, Option.bind_eq_some_iff] at hr
    obtain ⟨⟨middle, first⟩, hx, ⟨⟨outcome, last⟩, hy, final⟩⟩ := hr
    simp only [Option.some.injEq, Prod.mk.injEq] at final
    obtain ⟨rfl, rfl⟩ := final
    exact ih (action_typed hcall he instruction ha hx) hy
  | @switch scrut branches fallback left right rest kind hs _ _ _ _ ihLeft ihRight ihRest =>
    simp only [SourceEval.exec, Control.execWith, bind, Option.bind_eq_some_iff] at hr
    obtain ⟨⟨actual, middle⟩, hx, ⟨⟨selected, first⟩, hb, final⟩⟩ := hr
    have hm := scrutinee_typed he scrut hs hx
    have hselected : OutcomeTyped locals output selected :=
      Control.selectSource_spec actual branches fallback
        (fun _ h => ihLeft hm h) (fun _ h => ihRight hm h) hb
    cases selected with
    | returned value =>
      simp only [SourceEval.nextState, Option.some.injEq, Prod.mk.injEq] at final
      obtain ⟨rfl, rfl⟩ := final
      exact hselected
    | next resume =>
      simp only [SourceEval.nextState, Option.bind_eq_some_iff] at final
      obtain ⟨⟨outcome, last⟩, hz, final⟩ := final
      simp only [Option.some.injEq, Prod.mk.injEq] at final
      obtain ⟨rfl, rfl⟩ := final
      exact ihRest hselected hz

end SubtreeProofs.Rust.SourceEval.Types
