module

public import SubtreeProofs.Rust.SourcePartialTypeLocals
public import SubtreeProofs.Rust.SourceEvalTypedCode

/-! Successful expanded-source operands, expressions and actions preserve
independent partial-local types. Callee typing is an explicit local contract;
recursive discharge, addressed owners, initialization and loans are separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Types

open LookupSource Heap Partial

theorem operand_typed {locals : List Ty} {state after : State} (he : LocalsTyped locals state)
    (op : SourceEval.Operand) {ty : Ty} {value : Value}
    (ht : inferOperand locals op = some ty) (hr : operand state op = some (value, after)) :
    SnapshotTyped value ty ∧ LocalsTyped locals after := by
  cases op with
  | move place => exact he.move (inferMovePlace_read place ht) hr
  | copy place =>
    obtain ⟨rfl, hread, _⟩ := copy_nonowning hr
    cases hp : SourceTypes.inferPlace locals place with
    | none => simp [inferOperand, hp] at ht
    | some actual =>
      simp only [inferOperand, hp, bind, Option.bind] at ht
      split at ht
      next => cases ht; exact ⟨he.read hp hread, he⟩
      next => cases ht
  | boolean b =>
    cases ht
    cases hr
    exact ⟨.boolean b, he⟩
  | number n =>
    simp only [inferOperand] at ht
    split at ht
    next hb =>
      cases ht
      simp only [operand, hb, ite_true, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨.number hb, he⟩
    next => cases ht

theorem inferOperands_cons (locals : List Ty) (first : SourceEval.Operand) (rest : List SourceEval.Operand) :
    inferOperands locals (first :: rest) = (do
      let ty ← inferOperand locals first
      let types ← inferOperands locals rest
      pure (ty :: types)) := by
  simp only [inferOperands, List.mapM_cons]

theorem operands_typed {locals : List Ty} {state after : State} (he : LocalsTyped locals state)
    (args : List SourceEval.Operand) {types : List Ty} {values : List Value}
    (ht : inferOperands locals args = some types) (hr : operands state args = some (values, after)) :
    SnapshotFieldsTyped values types ∧ LocalsTyped locals after := by
  induction args generalizing state after types values with
  | nil => cases ht; cases hr; exact ⟨.nil, he⟩
  | cons first rest ih =>
    cases hf : inferOperand locals first with
    | none => simp [inferOperands_cons, hf] at ht
    | some firstTy =>
      cases hts : inferOperands locals rest with
      | none => simp [inferOperands_cons, hf, hts] at ht
      | some restTypes =>
        have htypes : types = firstTy :: restTypes := by
          simpa only [inferOperands_cons, hf, hts,
            bind, Option.bind, pure, Option.some.injEq] using ht.symm
        subst types
        cases hx : operand state first with
        | none => simp [operands, hx] at hr
        | some pair =>
          rcases pair with ⟨firstValue, middle⟩
          cases hy : operands middle rest with
          | none => simp [operands, hx, hy] at hr
          | some pair =>
            rcases pair with ⟨restValues, finalState⟩
            simp only [operands, hx, hy, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl⟩ := hr
            obtain ⟨hv, hm⟩ := operand_typed he first hf hx
            obtain ⟨hvs, ha⟩ := ih hm hts hy
            exact ⟨.cons hv hvs, ha⟩

theorem expression_typed {locals : List Ty} {state after : State} (he : LocalsTyped locals state)
    {expr : Expr} {ty : Ty} {value : Value} (ht : ExprConstraints locals expr ty)
    (hr : expression state expr = some (value, after)) : SnapshotTyped value ty ∧ LocalsTyped locals after := by
  cases ht with
  | use ht => exact operand_typed he _ ht hr
  | @address place inner ht =>
    simp only [expression] at hr
    cases hx : state.read place with
    | none => simp [hx] at hr
    | some target =>
      simp only [hx, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨.shared (he.read ht hx), he⟩
  | @aggregate kind variant args types result ht hs =>
    simp only [expression] at hr
    cases hx : operands state args with
    | none => simp [hx] at hr
    | some pair =>
      rcases pair with ⟨values, middle⟩
      simp only [hx, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨hvs, ha⟩ := operands_typed he _ ht hx
      exact ⟨.node hs hvs, ha⟩
  | @less left right hl hrTy =>
    simp only [expression] at hr
    cases hx : operand state left with
    | none => simp [hx] at hr
    | some pair =>
      rcases pair with ⟨leftValue, middle⟩
      cases hy : operand middle right with
      | none => simp [hx, hy] at hr
      | some pair =>
        rcases pair with ⟨rightValue, finalState⟩
        obtain ⟨_, hm⟩ := operand_typed he left hl hx
        obtain ⟨_, ha⟩ := operand_typed hm right hrTy hy
        cases leftValue with
        | boolean _ | reference _ | boxed _ | node _ _ _ => simp [hx, hy] at hr
        | number leftNumber =>
          cases rightValue with
          | boolean _ | reference _ | boxed _ | node _ _ _ => simp [hx, hy] at hr
          | number rightNumber =>
            simp only [hx, hy, bind, Option.bind] at hr
            cases hc : less32 leftNumber rightNumber with
            | none => simp [hc] at hr
            | some answer =>
              simp only [hc, Option.some.injEq, Prod.mk.injEq] at hr
              obtain ⟨rfl, rfl⟩ := hr
              exact ⟨.boolean answer, ha⟩

def CallsTyped (call : Calls) : Prop :=
  ∀ function args types value cost ty, SnapshotFieldsTyped args types → callOutput function types = some ty →
    call function args = some (value, cost) → SnapshotTyped value ty

theorem action_typed {call : Calls} (hcall : CallsTyped call)
    {locals : List Ty} {state after : State} {cost : SourceEval.Cost}
    (he : LocalsTyped locals state) (instruction : SourceEval.Action)
    (ht : ActionConstraints locals instruction) (hr : action call state instruction = some (after, cost)) :
    LocalsTyped locals after := by
  cases instruction with
  | storageLive slot | storageDead slot => cases hr; exact he.clear slot
  | drop slot => cases hr; exact he.clear slot
  | fakeRead place => cases hr; exact he
  | undefinedBehavior => cases hr
  | assign slot rhs =>
    obtain ⟨ty, hd, hxTy⟩ := ht
    simp only [action] at hr
    cases hx : expression state rhs with
    | none => simp [hx] at hr
    | some pair =>
      rcases pair with ⟨value, next⟩
      simp only [hx, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨hv, he'⟩ := expression_typed he hxTy hx
      exact he'.store hd (ofValue_typed hv)
  | call function args slot =>
    obtain ⟨types, ty, ha, hc, hd⟩ := ht
    simp only [action] at hr
    cases hx : operands state args with
    | none => simp [hx] at hr
    | some pair =>
      rcases pair with ⟨values, next⟩
      cases hy : call function values with
      | none => simp [hx, hy] at hr
      | some pair =>
        rcases pair with ⟨value, inner⟩
        simp only [hx, hy, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        obtain ⟨hvs, he'⟩ := operands_typed he args ha hx
        exact he'.store hd (ofValue_typed (hcall function values types value inner ty hvs hc hy))

end SubtreeProofs.Rust.SourceEval.Types
