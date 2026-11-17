module

public import SubtreeProofs.Rust.LookupTypePrimitives
public import SubtreeProofs.Rust.LookupHeapExecution

/-! Successful execution preserves the independently declared local types.
Callee contracts are local; recursive discharge is provided separately. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.SourceTypes

open Heap

def CallsTyped (call : Calls) : Prop :=
  ∀ function cells types memory cell after cost ty,
    FieldsTyped memory cells types → callOutput function types = some ty →
    call function cells memory = some (cell, after, cost) →
    Typed after cell ty ∧ Extends memory after

theorem action_typed {call : Calls} (hcall : CallsTyped call)
    {memory after : Memory} {locals : List Ty} {env env' : Locals} {cost : Cost}
    (he : EnvTyped memory locals env) (instruction : Action)
    (ht : ActionConstraints locals instruction)
    (hr : action call memory env instruction = some (env', after, cost)) :
    EnvTyped after locals env' ∧ Extends memory after := by
  cases instruction with
  | scope slot => cases hr; exact ⟨he.clear slot, .refl memory⟩
  | dropMoved slot =>
    simp only [action] at hr
    cases hn : env slot with
    | some _ => simp [hn] at hr
    | none =>
      simp only [hn, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      exact ⟨he, .refl memory⟩
  | assign slot rhs =>
    obtain ⟨ty, hs, hd⟩ := ht
    simp only [action] at hr
    cases hx : rvalue memory env rhs with
    | none => simp [hx] at hr
    | some pair =>
      rcases pair with ⟨value, next⟩
      simp only [hx, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      obtain ⟨hv, he'⟩ := rvalue_typed he rhs hs hx
      exact ⟨he'.store hd hv, .refl memory⟩
  | call function args slot =>
    obtain ⟨types, ty, hs, hc, hd⟩ := ht
    simp only [action] at hr
    cases hx : operands memory args env with
    | none => simp [hx] at hr
    | some pair =>
      rcases pair with ⟨values, next⟩
      cases hy : call function values memory with
      | none => simp [hx, hy] at hr
      | some pair =>
        rcases pair with ⟨value, mem, inner⟩
        simp only [hx, hy, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl, rfl⟩ := hr
        obtain ⟨hvs, he'⟩ := operands_typed he args hs hx
        obtain ⟨hv, hex⟩ := hcall function values types memory value mem inner ty hvs hc hy
        exact ⟨(he'.mono hex).store hd hv, hex⟩

def OutcomeTyped (memory : Memory) (locals : List Ty) (output : Ty) : Result → Prop
  | .next env => EnvTyped memory locals env
  | .returned cell => Typed memory cell output

theorem exec_typed {call : Calls} (hcall : CallsTyped call) (code : Code)
    {memory after : Memory} {locals : List Ty} {output : Ty} {env : Locals}
    {result : Result} {cost : Cost} (he : EnvTyped memory locals env)
    (ht : CodeConstraints locals output code)
    (hr : Heap.exec call code memory env = some (result, after, cost)) :
    OutcomeTyped after locals output result ∧ Extends memory after := by
  induction ht generalizing memory after env result cost with
  | done => cases hr; exact ⟨he, .refl memory⟩
  | ret hret =>
    simp only [Heap.exec] at hr
    cases hx : env 0 with
    | none => simp [hx] at hr
    | some value =>
      simp only [hx, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      exact ⟨he.get hx hret, .refl memory⟩
  | @step instruction rest ha ht ih =>
    simp only [Heap.exec] at hr
    cases hx : action call memory env instruction with
    | none => simp [hx] at hr
    | some pair =>
      rcases pair with ⟨next, mem, first⟩
      cases hy : Heap.exec call rest mem next with
      | none => simp [hx, hy] at hr
      | some pair =>
        rcases pair with ⟨lastResult, lastMemory, last⟩
        simp only [hx, hy, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl, rfl⟩ := hr
        obtain ⟨he', hex⟩ := action_typed hcall he instruction ha hx
        obtain ⟨hout, hex'⟩ := ih he' hy
        exact ⟨hout, hex.trans hex'⟩
  | @branch scrut key other yes no rest kind hs hk ho hy hn ht ihYes ihNo ihRest =>
    simp only [Heap.exec] at hr
    cases hx : scrutinee memory env scrut with
    | none => simp [hx] at hr
    | some pair =>
      rcases pair with ⟨actual, next⟩
      cases hb : selectBranch actual key other
          (fun _ => Heap.exec call yes memory next) (fun _ => Heap.exec call no memory next) with
      | none => simp [hx, hb] at hr
      | some pair =>
        rcases pair with ⟨selected, mem, first⟩
        have he' := scrutinee_typed he scrut hs hx
        have hselected : OutcomeTyped mem locals output selected ∧ Extends memory mem := by
          by_cases ha : actual = key
          · exact ihYes he' (by simpa only [selectBranch, ha, ite_true] using hb)
          · by_cases ha' : other.all (· = actual) = true
            · exact ihNo he' (by simpa only [selectBranch, ha, ite_false, ha', ite_true] using hb)
            · simp [selectBranch, ha, ha'] at hb
        cases selected with
        | returned value =>
          simp only [hx, hb, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          exact hselected
        | next resume =>
          simp only [hx, hb, bind, Option.bind] at hr
          cases hz : Heap.exec call rest mem resume with
          | none => simp [hz] at hr
          | some pair =>
            rcases pair with ⟨lastResult, lastMemory, last⟩
            simp only [hz, Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl, rfl⟩ := hr
            obtain ⟨hout, hex⟩ := ihRest hselected.1 hz
            exact ⟨hout, hselected.2.trans hex⟩

end SubtreeProofs.Rust.LookupSource.SourceTypes
