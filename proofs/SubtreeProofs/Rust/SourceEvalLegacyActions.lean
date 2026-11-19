module

public import SubtreeProofs.Rust.SourceEvalLegacyValues
public import SubtreeProofs.Rust.SourceEvalMachine

/-! Exact old-to-expanded statement simulation. Successful old drops have
empty locals, so this fragment adds neither destruction nor evaluator calls.
Callee correspondence remains explicit and is discharged by recursive drivers. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Legacy

open LookupSource LookupSource.Partial

def costMap (cost : LookupSource.Cost) : SourceEval.Cost := ⟨cost, {}, 0⟩

theorem costMap_plus (first last : LookupSource.Cost) :
    costMap (first.plus last) = (costMap first).plus (costMap last) := rfl

theorem costMap_local (steps : Nat) : costMap ⟨steps, {}⟩ = Cost.local steps := rfl

def actionMap {F : Type} (functionMap : F → SourceEval.Function) : Control.Action F → SourceEval.Action
  | .storageLive slot => .storageLive slot
  | .storageDead slot => .storageDead slot
  | .assign slot expr => .assign slot (exprMap expr)
  | .call function args slot => .call (functionMap function) (args.map operandMap) slot
  | .dropConditional slot => .drop slot

def CallsRefine {F : Type} (functionMap : F → SourceEval.Function)
    (oldCall : CalleesFor F) (newCall : Calls) : Prop :=
  ∀ function args value cost, FieldsBounded args → oldCall function args = some (value, cost) →
    Bounded value ∧ newCall (functionMap function) args = some (value, costMap cost)

theorem actionMap_weight {F : Type} (functionMap : F → SourceEval.Function) (act : Control.Action F) :
    (actionMap functionMap act).weight = act.lower.weight := by
  cases act with
  | storageLive _ | storageDead _ | dropConditional _ => rfl
  | assign slot expr => simp only [actionMap, Action.weight, Control.Action.lower,
      LookupSource.Action.weight, exprMap_weight]
  | call fn args slot =>
    simp only [actionMap, Action.weight, Control.Action.lower, LookupSource.Action.weight, List.map_map]
    congr 2
    exact List.map_congr_left (fun op _ => operandMap_weight op)

theorem action_refines {F : Type} {functionMap : F → SourceEval.Function}
    {oldCall : CalleesFor F} {newCall : Calls} (hc : CallsRefine functionMap oldCall newCall)
    {env after : Env} (hb : EnvBounded env) (act : Control.Action F) {cost : LookupSource.Cost}
    (hr : act.exec oldCall env = some (after, cost)) :
    SourceEval.action newCall (Locals.lift env) (actionMap functionMap act) =
      some (Locals.lift after, costMap cost) ∧ EnvBounded after := by
  cases act with
  | storageLive slot | storageDead slot =>
    simp only [Control.Action.exec, Control.Action.lower, evalAction,
      Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨by simp only [actionMap, SourceEval.action, lift_set]; rfl, hb.clear slot⟩
  | assign slot expr =>
    simp only [Control.Action.exec, Control.Action.lower, evalAction] at hr
    cases he : evalRValue env expr with
    | none => simp [he] at hr
    | some pair =>
      rcases pair with ⟨value, middle⟩
      simp only [he, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨hm, hv, hb'⟩ := expression_refines hb expr he
      refine ⟨?_, hb'.set slot (by intro v heq; cases heq; exact hv)⟩
      simp only [actionMap, SourceEval.action, hm, bind, Option.bind]
      have hw := actionMap_weight functionMap (.assign slot expr)
      simp only [actionMap, Control.Action.lower] at hw
      rw [hw, lift_set]
      rfl
  | call fn args slot =>
    simp only [Control.Action.exec, Control.Action.lower, evalAction] at hr
    cases he : evalOperands args env with
    | none => simp [he] at hr
    | some pair =>
      rcases pair with ⟨values, middle⟩
      cases hf : oldCall fn values with
      | none => simp [he, hf] at hr
      | some pair =>
        rcases pair with ⟨value, work⟩
        simp only [he, hf, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        obtain ⟨hm, hvs, hb'⟩ := operands_refines args hb he
        obtain ⟨hv, hc'⟩ := hc fn values value work hvs hf
        refine ⟨?_, hb'.set slot (by intro v heq; cases heq; exact hv)⟩
        simp only [actionMap, SourceEval.action, hm, hc', bind, Option.bind]
        have hw := actionMap_weight functionMap (.call fn args slot)
        simp only [actionMap, Control.Action.lower] at hw
        rw [hw, costMap_plus, lift_set]
        rfl
  | dropConditional slot =>
    simp only [Control.Action.exec, Control.Action.lower, evalAction] at hr
    cases he : env slot with
    | some value => simp [he] at hr
    | none =>
      simp only [he, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      refine ⟨?_, hb⟩
      have hs : (Locals.lift env).set slot .empty = Locals.lift env := by
        funext index
        by_cases hi : index = slot <;> simp [Locals.set, Locals.lift, hi, he]
      simp only [actionMap, SourceEval.action_drop, hs, Locals.lift, he, Slot.dropWork]
      rfl

theorem scrutinee_refines {env after : Env} (hb : EnvBounded env) (scrut : LookupSource.Scrutinee)
    {key : Key} (hr : evalScrutinee env scrut = some (key, after)) :
    SourceEval.scrutinee (Locals.lift env) scrut = some (key, Locals.lift after) ∧ EnvBounded after := by
  cases scrut with
  | value op =>
    simp only [evalScrutinee] at hr
    cases he : evalOperand env op with
    | none => simp [he] at hr
    | some pair =>
      rcases pair with ⟨value, middle⟩
      obtain ⟨hm, _, hb'⟩ := operand_refines hb op he
      simp only [he, bind, Option.bind] at hr
      cases value with
      | boolean b =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        refine ⟨?_, hb'⟩
        cases op <;> simp only [operandMap] at hm <;>
          simp only [SourceEval.scrutinee, hm, bind, Option.bind]
      | number _ | node _ _ _ | reference _ | boxed _ => cases hr
  | discriminant place =>
    simp only [evalScrutinee] at hr
    cases he : readPlace env place with
    | none => simp [he] at hr
    | some value =>
      simp only [he, bind, Option.bind] at hr
      cases value with
      | node kind variant fields =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ⟨by simp only [SourceEval.scrutinee, Locals.get_lift he, Slot.ofValue, bind, Option.bind], hb⟩
      | boolean _ | number _ | reference _ | boxed _ => cases hr

end SubtreeProofs.Rust.SourceEval.Legacy
