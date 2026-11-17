module

public import SubtreeProofs.Rust.SourcePartialReadback
public import SubtreeProofs.Rust.SourceEvalOperands

/-! The explicit numeric domain needed when embedding the earlier snapshot
profile: old numbers are arbitrary naturals, while evaluator scalar copies
require u32 width. This is only numeric validity, not a replacement type system. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Legacy

open LookupSource LookupSource.Partial

mutual
  inductive Bounded : Value → Prop where
    | boolean (value : Bool) : Bounded (.boolean value)
    | number {value : Nat} : value < 2^32 → Bounded (.number value)
    | node {kind : Kind} {variant : Nat} {fields : List Value} : FieldsBounded fields → Bounded (.node kind variant fields)
    | reference {value : Value} : Bounded value → Bounded (.reference value)
    | boxed {value : Value} : Bounded value → Bounded (.boxed value)

  inductive FieldsBounded : List Value → Prop where
    | nil : FieldsBounded []
    | cons {value : Value} {values : List Value} : Bounded value → FieldsBounded values → FieldsBounded (value :: values)
end

def EnvBounded (env : Env) : Prop := ∀ slot value, env slot = some value → Bounded value

theorem FieldsBounded.get {values : List Value} (h : FieldsBounded values) (index : Nat) {value : Value}
    (hg : values[index]? = some value) : Bounded value := by
  induction index generalizing values with
  | zero => cases h with
    | nil => cases hg
    | cons first _ => cases hg; exact first
  | succ index ih => cases h with
    | nil => cases hg
    | cons _ rest => exact ih rest hg

theorem EnvBounded.set {env : Env} (h : EnvBounded env) (slot : Nat) {value : Option Value}
    (hv : ∀ v, value = some v → Bounded v) : EnvBounded (env.set slot value) := by
  intro index v hs
  by_cases hi : index = slot
  · exact hv v (by simpa only [Env.set, hi, ite_true] using hs)
  · exact h index v (by simpa only [Env.set, hi, ite_false] using hs)

theorem EnvBounded.clear {env : Env} (h : EnvBounded env) (slot : Nat) : EnvBounded (env.set slot none) :=
  h.set slot (by intro v hv; cases hv)

theorem readPlace_bounded {env : Env} (h : EnvBounded env) (place : Place) {value : Value}
    (hr : readPlace env place = some value) : Bounded value := by
  induction place generalizing value with
  | «local» slot => exact h slot value hr
  | deref parent ih =>
    simp only [readPlace] at hr
    cases hp : readPlace env parent with
    | none => simp [hp] at hr
    | some holder =>
      have hb := ih hp
      simp only [hp, bind, Option.bind] at hr
      cases hb <;> try contradiction
      all_goals cases hr; assumption
  | field parent variant index ih =>
    simp only [readPlace] at hr
    cases hp : readPlace env parent with
    | none => simp [hp] at hr
    | some holder =>
      have hb := ih hp
      simp only [hp, bind, Option.bind] at hr
      cases hb with
      | @node kind actual fields bounded =>
        by_cases hv : variant.all (· = actual) = true
        · simp only [hv, ite_true] at hr
          exact bounded.get index hr
        · simp only [hv] at hr
          cases hr
      | boolean _ | number _ | reference _ | boxed _ => cases hr

def operandMap : LookupSource.Operand → SourceEval.Operand
  | .move slot => .move (.local slot)
  | .copy place => .copy place
  | .boolean value => .boolean value

def exprMap : RValue → Expr
  | .use op => .use (operandMap op)
  | .address place => .address place
  | .aggregate kind variant args => .aggregate kind variant (args.map operandMap)

theorem lift_set (env : Env) (slot : Nat) (value : Option Value) :
    Partial.Locals.lift (env.set slot value) = (Partial.Locals.lift env).set slot
      (value.map Slot.ofValue |>.getD .empty) := by
  cases value <;> funext index <;> by_cases hi : index = slot <;>
    simp [Partial.Locals.lift, Partial.Locals.set, Env.set, hi]

theorem operand_refines {env after : Env} (hb : EnvBounded env) (op : LookupSource.Operand) {value : Value}
    (hr : evalOperand env op = some (value, after)) :
    SourceEval.operand (Partial.Locals.lift env) (operandMap op) = some (value, Partial.Locals.lift after) ∧
      Bounded value ∧ EnvBounded after := by
  cases op with
  | move slot =>
    have ht := Partial.Locals.move_local_lift env slot
    rw [hr] at ht
    simp only [evalOperand] at hr
    cases he : env slot with
    | none => simp [he] at hr
    | some result =>
      simp only [he, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨ht, hb slot result he, hb.clear slot⟩
  | boolean value => cases hr; exact ⟨rfl, .boolean value, hb⟩
  | copy place =>
    simp only [evalOperand] at hr
    cases he : readPlace env place with
    | none => simp [he] at hr
    | some result =>
      have hv := readPlace_bounded hb place he
      simp only [he, bind, Option.bind] at hr
      cases hv with
      | boolean b =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ⟨by simp only [operandMap, SourceEval.operand, Partial.Locals.read_lift, he, bind, Option.bind],
          .boolean b, hb⟩
      | reference child =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ⟨by simp only [operandMap, SourceEval.operand, Partial.Locals.read_lift, he, bind, Option.bind],
          .reference child, hb⟩
      | number hn =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ⟨by simp only [operandMap, SourceEval.operand, Partial.Locals.read_lift, he, bind, Option.bind, hn, ite_true],
          .number hn, hb⟩
      | node _ | boxed _ => cases hr


theorem operands_refines (ops : List LookupSource.Operand) {env after : Env} (hb : EnvBounded env)
    {values : List Value} (hr : evalOperands ops env = some (values, after)) :
    SourceEval.operands (Partial.Locals.lift env) (ops.map operandMap) =
      some (values, Partial.Locals.lift after) ∧ FieldsBounded values ∧ EnvBounded after := by
  induction ops generalizing env values with
  | nil => cases hr; exact ⟨rfl, .nil, hb⟩
  | cons op ops ih =>
    simp only [evalOperands] at hr
    cases ho : evalOperand env op with
    | none => simp [ho] at hr
    | some pair =>
      rcases pair with ⟨value, middle⟩
      cases hs : evalOperands ops middle with
      | none => simp [ho, hs] at hr
      | some pair =>
        rcases pair with ⟨rest, next⟩
        simp only [ho, hs, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        obtain ⟨hop, hv, hm⟩ := operand_refines hb op ho
        obtain ⟨hops, hvs, hn⟩ := ih hm hs
        exact ⟨by simp only [List.map_cons, SourceEval.operands, hop, hops, bind, Option.bind],
          .cons hv hvs, hn⟩

theorem expression_refines {env after : Env} (hb : EnvBounded env) (expr : RValue) {value : Value}
    (hr : evalRValue env expr = some (value, after)) :
    SourceEval.expression (Partial.Locals.lift env) (exprMap expr) = some (value, Partial.Locals.lift after) ∧
      Bounded value ∧ EnvBounded after := by
  cases expr with
  | use op => exact operand_refines hb op hr
  | address place =>
    simp only [evalRValue] at hr
    cases he : readPlace env place with
    | none => simp [he] at hr
    | some result =>
      simp only [he, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨by simp only [exprMap, SourceEval.expression, Partial.Locals.read_lift, he, bind, Option.bind],
        .reference (readPlace_bounded hb place he), hb⟩
  | aggregate kind variant ops =>
    simp only [evalRValue] at hr
    cases he : evalOperands ops env with
    | none => simp [he] at hr
    | some pair =>
      rcases pair with ⟨values, next⟩
      simp only [he, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨hops, hvs, hn⟩ := operands_refines ops hb he
      exact ⟨by simp only [exprMap, SourceEval.expression, hops, bind, Option.bind], .node hvs, hn⟩

theorem operandMap_weight (op : LookupSource.Operand) : (operandMap op).weight = op.weight := by
  cases op <;> rfl

theorem exprMap_weight (expr : RValue) : (exprMap expr).weight = expr.weight := by
  cases expr with
  | use op => exact operandMap_weight op
  | address place => exact Nat.add_comm _ _
  | aggregate kind variant ops =>
    simp only [exprMap, Expr.weight, RValue.weight, List.map_map]
    congr 2
    exact List.map_congr_left (fun op _ => operandMap_weight op)

end SubtreeProofs.Rust.SourceEval.Legacy
