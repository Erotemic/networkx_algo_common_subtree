module

public import SubtreeProofs.Rust.LookupStackState
public import SubtreeProofs.Rust.LookupHeapExecution

/-! Initialization-state preservation for actual successful heap primitives.
Storage status is exact along a path, independently of value typing and Box
ownership. Allocated empty slots remain allocated when a value is moved out. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Stack

open Heap

def baseSlot : Place → Nat
  | .local slot => slot
  | .deref parent | .field parent _ _ => baseSlot parent

theorem placeReady_sound {state : State} (place : Place) (h : placeReady state place = true) :
    status state (baseSlot place) = .full := by
  induction place with
  | «local» slot => simpa [placeReady, baseSlot] using h
  | deref parent ih | field parent variant index ih => exact ih h

theorem StateRep.initialized {state : State} {env : Locals} (h : StateRep state env)
    {slot : Nat} (hs : status state slot = .full) : ∃ cell, env slot = some cell := by
  have hx := h slot
  rw [hs] at hx
  cases hc : env slot with
  | none => rw [hc] at hx; cases hx
  | some cell => exact ⟨cell, rfl⟩

theorem operands_length {memory : Memory} {env env' : Locals} (args : List Operand) {cells : List Cell}
    (hr : operands memory args env = some (cells, env')) : cells.length = args.length := by
  induction args generalizing env env' cells with
  | nil => cases hr; rfl
  | cons first rest ih =>
    simp only [operands] at hr
    cases hc : operand memory env first with
    | none => simp [hc] at hr
    | some pair =>
      rcases pair with ⟨cell, middle⟩
      cases hs : operands memory rest middle with
      | none => simp [hc, hs] at hr
      | some pair =>
        rcases pair with ⟨vs, final⟩
        simp only [hc, hs, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact congrArg Nat.succ (ih hs)

theorem operand_sound {state next : State} {memory : Memory} {env env' : Locals}
    (he : StateRep state env) (op : Operand) {cell : Cell}
    (hs : inferOperand state op = some next) (hr : operand memory env op = some (cell, env')) :
    StateRep next env' := by
  cases op with
  | move slot =>
    simp only [inferOperand] at hs
    split at hs
    next hb =>
      have hslot : slot < state.length := by simpa using (Bool.and_eq_true_iff.mp hb).1
      cases hs
      simp only [operand] at hr
      cases hc : env slot with
      | none => simp [hc] at hr
      | some value =>
        simp only [hc, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact he.set slot hslot trivial
    next => cases hs
  | boolean value => cases hs; cases hr; exact he
  | copy place =>
    simp only [inferOperand] at hs
    split at hs
    next =>
      cases hs
      simp only [operand] at hr
      cases hl : locate memory env place with
      | none => simp [hl] at hr
      | some pair =>
        rcases pair with ⟨value, address⟩
        simp only [hl, bind, Option.bind] at hr
        cases value <;> try contradiction
        all_goals
          simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          exact he
    next => cases hs

theorem operands_sound {state next : State} {memory : Memory} {env env' : Locals}
    (he : StateRep state env) (args : List Operand) {cells : List Cell}
    (hs : inferOperands state args = some next) (hr : operands memory args env = some (cells, env')) :
    StateRep next env' := by
  induction args generalizing state next env env' cells with
  | nil => cases hs; cases hr; exact he
  | cons first rest ih =>
    simp only [inferOperands] at hs
    cases hf : inferOperand state first with
    | none => simp [hf] at hs
    | some middle =>
      simp only [hf, bind, Option.bind] at hs
      simp only [operands] at hr
      cases hc : operand memory env first with
      | none => simp [hc] at hr
      | some pair =>
        rcases pair with ⟨value, localState⟩
        cases hcs : operands memory rest localState with
        | none => simp [hc, hcs] at hr
        | some pair =>
          rcases pair with ⟨vs, final⟩
          simp only [hc, hcs, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          exact ih (operand_sound he first hf hc) hs hcs

theorem rvalue_sound {state next : State} {memory : Memory} {env env' : Locals}
    (he : StateRep state env) (rhs : RValue) {cell : Cell}
    (hs : inferRValue state rhs = some next) (hr : rvalue memory env rhs = some (cell, env')) :
    StateRep next env' := by
  cases rhs with
  | use op => exact operand_sound he op hs hr
  | address place =>
    simp only [inferRValue] at hs
    split at hs
    next =>
      cases hs
      simp only [rvalue] at hr
      cases hc : borrow memory env place with
      | none => simp [hc] at hr
      | some value =>
        simp only [hc, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact he
    next => cases hs
  | aggregate kind variant args =>
    simp only [rvalue] at hr
    cases hc : operands memory args env with
    | none => simp [hc] at hr
    | some pair =>
      rcases pair with ⟨values, final⟩
      simp only [hc, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact operands_sound he args hs hc

theorem scrutinee_sound {state next : State} {memory : Memory} {env env' : Locals}
    (he : StateRep state env) (scrut : Scrutinee) {key : Key}
    (hs : inferScrutinee state scrut = some next) (hr : scrutinee memory env scrut = some (key, env')) :
    StateRep next env' := by
  cases scrut with
  | discriminant place =>
    simp only [inferScrutinee] at hs
    split at hs
    next =>
      cases hs
      simp only [scrutinee] at hr
      cases hl : locate memory env place with
      | none => simp [hl] at hr
      | some pair =>
        rcases pair with ⟨value, address⟩
        simp only [hl, bind, Option.bind] at hr
        cases value <;> try contradiction
        simp only [Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact he
    next => cases hs
  | value op =>
    simp only [scrutinee] at hr
    cases hc : operand memory env op with
    | none => simp [hc] at hr
    | some pair =>
      rcases pair with ⟨value, final⟩
      have he' := operand_sound he op hs hc
      simp only [hc, bind, Option.bind] at hr
      cases value <;> try contradiction
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact he'

theorem store_spec {state next : State} {env : Locals} {slot : Nat} (he : StateRep state env)
    (hs : store state slot = some next) (cell : Cell) :
    StateRep next (env.set slot (some cell)) ∧ status state slot ≠ .dead := by
  unfold store at hs
  split at hs
  next hb =>
    have hh := Bool.and_eq_true_iff.mp hb
    have hslot : slot < state.length := by simpa using hh.1
    have hlive : status state slot ≠ .dead := by simpa using hh.2
    cases hs
    exact ⟨he.set slot hslot trivial, hlive⟩
  next => cases hs

theorem initial_rep (count : Nat) (cells : List Cell) : StateRep (initial count cells.length) (initialLocals cells) := by
  intro index
  cases index with
  | zero => trivial
  | succ index =>
    change Matches ((List.replicate cells.length Status.full ++
      List.replicate (count - (cells.length + 1)) Status.dead)[index]?.getD .dead) cells[index]?
    by_cases hi : index < cells.length
    · rw [List.getElem?_append_left (by simpa using hi)]
      simp only [List.getElem?_replicate, hi, ite_true, Option.getD_some]
      cases hc : cells[index]? with
      | none => have hn := List.getElem?_eq_none_iff.mp hc; omega
      | some cell => trivial
    · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt hi)]
      rw [List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hi)]
      simp only [List.getElem?_replicate]
      split <;> trivial

end SubtreeProofs.Rust.LookupSource.Stack
