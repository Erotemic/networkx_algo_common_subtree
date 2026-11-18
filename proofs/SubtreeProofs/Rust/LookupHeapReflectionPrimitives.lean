module

public import SubtreeProofs.Rust.LookupHeapPrimitives

/-! Successful concrete helper primitives reflect into the independent source
semantics from the existing exact local representation. No native depth bound
or desired source result is supplied. The older forward simulation is reused
for pointer locations and subsequent whole-run resource consequences. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap

theorem option_source {memory : Memory} {cell : Option Cell} {value : Option Value}
    (h : Option.Rel (Represents memory) cell value) {actual : Cell} (hc : cell = some actual) :
    ∃ source, value = some source ∧ Represents memory actual source := by
  rw [hc] at h
  cases h with
  | some hv => exact ⟨_, rfl, hv⟩

theorem EnvRep.source {memory : Memory} {concrete : Locals} {abstract : Env}
    (h : EnvRep memory concrete abstract) {slot : Nat} {cell : Cell} (hc : concrete slot = some cell) :
    ∃ value, abstract slot = some value ∧ Represents memory cell value :=
  option_source (h slot) hc

theorem locate_reflect {memory : Memory} {concrete : Locals} {abstract : Env}
    (he : EnvRep memory concrete abstract) (place : Place) {cell : Cell} {address : Option Pointer}
    (hr : locate memory concrete place = some (cell, address)) :
    ∃ value, readPlace abstract place = some value ∧ Represents memory cell value := by
  induction place generalizing cell address with
  | «local» slot =>
    cases hc : concrete slot with
    | none => simp [locate, hc] at hr
    | some actual =>
      simp only [locate, hc, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact he.source hc
  | deref place ih =>
    cases hp : locate memory concrete place with
    | none => simp [locate, hp] at hr
    | some pair =>
      rcases pair with ⟨parent, location⟩
      obtain ⟨value, hs, hv⟩ := ih hp
      cases hv with
      | boolean _ | number _ | node _ => simp [locate, hp] at hr
      | shared hread hchild =>
        simp only [locate, hp, hread, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ⟨_, by simp only [readPlace, hs, Bind.bind, Option.bind], hchild⟩
      | owned hread hchild =>
        simp only [locate, hp, hread, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ⟨_, by simp only [readPlace, hs, Bind.bind, Option.bind], hchild⟩
  | field place variant index ih =>
    cases hp : locate memory concrete place with
    | none => simp [locate, hp] at hr
    | some pair =>
      rcases pair with ⟨parent, location⟩
      obtain ⟨value, hs, hv⟩ := ih hp
      cases hv with
      | boolean _ | number _ | shared _ _ | owned _ _ => simp [locate, hp] at hr
      | @node kind actual cells values hfields =>
        by_cases hb : variant.all (· = actual) = true
        · cases hg : cells[index]? with
          | none => simp [locate, hp, hb, hg] at hr
          | some selected =>
            simp only [locate, hp, hb, ite_true, hg, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl⟩ := hr
            obtain ⟨source, ht, hrep⟩ := option_source (hfields.get index) hg
            exact ⟨source, by simp only [readPlace, hs, hb, ite_true, ht, Bind.bind, Option.bind], hrep⟩
        · simp [locate, hp, hb] at hr

theorem borrow_reflect {memory : Memory} {concrete : Locals} {abstract : Env}
    (he : EnvRep memory concrete abstract) (place : Place) {cell : Cell}
    (hr : borrow memory concrete place = some cell) :
    ∃ value, evalRValue abstract (.address place) = some (.reference value, abstract) ∧
      Represents memory cell (.reference value) := by
  cases hl : locate memory concrete place with
  | none => simp [borrow, hl] at hr
  | some pair =>
    rcases pair with ⟨target, address⟩
    cases address with
    | none => simp [borrow, hl] at hr
    | some pointer =>
      simp only [borrow, hl, Bind.bind, Option.bind, pure, Option.some.injEq] at hr
      subst cell
      obtain ⟨value, hs, hv⟩ := locate_reflect he place hl
      obtain ⟨found, location, hx, _, hread⟩ := locate_spec he place hs
      rw [hl] at hx
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hx)
      exact ⟨value, by simp only [evalRValue, hs, Bind.bind, Option.bind], .shared (hread pointer rfl) hv⟩

theorem operand_reflect {memory : Memory} {concrete next : Locals} {abstract : Env}
    (he : EnvRep memory concrete abstract) (op : Operand) {cell : Cell}
    (hr : operand memory concrete op = some (cell, next)) :
    ∃ value after, evalOperand abstract op = some (value, after) ∧
      Represents memory cell value ∧ EnvRep memory next after := by
  cases op with
  | move slot =>
    cases hs : concrete slot with
    | none => simp [operand, hs] at hr
    | some actual =>
      simp only [operand, hs, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨value, hv, hrep⟩ := he.source hs
      exact ⟨value, abstract.set slot none, by simp only [evalOperand, hv, Bind.bind, Option.bind], hrep, he.set slot .none⟩
  | boolean b =>
    cases hr
    exact ⟨.boolean b, abstract, rfl, .boolean b, he⟩
  | copy place =>
    cases hl : locate memory concrete place with
    | none => simp [operand, hl] at hr
    | some pair =>
      rcases pair with ⟨parent, location⟩
      obtain ⟨value, hs, hv⟩ := locate_reflect he place hl
      cases hv with
      | node _ | owned _ _ => simp [operand, hl] at hr
      | boolean _ | number _ | shared _ _ =>
        all_goals
          simp only [operand, hl, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          refine ⟨_, abstract, ?_, by constructor <;> assumption, he⟩
          simp only [evalOperand, hs, Bind.bind, Option.bind]

theorem operands_reflect {memory : Memory} {concrete next : Locals} {abstract : Env}
    (he : EnvRep memory concrete abstract) (args : List Operand) {cells : List Cell}
    (hr : operands memory args concrete = some (cells, next)) :
    ∃ values after, evalOperands args abstract = some (values, after) ∧
      RepresentsFields memory cells values ∧ EnvRep memory next after := by
  induction args generalizing concrete next abstract cells with
  | nil => cases hr; exact ⟨[], abstract, rfl, .nil, he⟩
  | cons op rest ih =>
    simp only [operands, Bind.bind, Option.bind_eq_some_iff] at hr
    obtain ⟨⟨cell, middle⟩, ho, ⟨⟨tail, final⟩, ht, hf⟩⟩ := hr
    simp only [Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    obtain ⟨value, sourceMiddle, hs, hv, hm⟩ := operand_reflect he op ho
    obtain ⟨values, sourceFinal, hts, hvs, hend⟩ := ih hm ht
    exact ⟨value :: values, sourceFinal, by simp only [evalOperands, hs, hts, Bind.bind, Option.bind], .cons hv hvs, hend⟩

theorem rvalue_reflect {memory : Memory} {concrete next : Locals} {abstract : Env}
    (he : EnvRep memory concrete abstract) (rhs : RValue) {cell : Cell}
    (hr : rvalue memory concrete rhs = some (cell, next)) :
    ∃ value after, evalRValue abstract rhs = some (value, after) ∧
      Represents memory cell value ∧ EnvRep memory next after := by
  cases rhs with
  | use op => exact operand_reflect he op hr
  | address place =>
    cases hb : borrow memory concrete place with
    | none => simp [rvalue, hb] at hr
    | some actual =>
      simp only [rvalue, hb, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨value, hs, hv⟩ := borrow_reflect he place hb
      exact ⟨_, abstract, hs, hv, he⟩
  | aggregate kind variant args =>
    cases hs : operands memory args concrete with
    | none => simp [rvalue, hs] at hr
    | some pair =>
      rcases pair with ⟨cells, state⟩
      simp only [rvalue, hs, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨values, after, ht, hv, he'⟩ := operands_reflect he args hs
      exact ⟨_, after, by simp only [evalRValue, ht, Bind.bind, Option.bind], .node hv, he'⟩

theorem scrutinee_reflect {memory : Memory} {concrete next : Locals} {abstract : Env}
    (he : EnvRep memory concrete abstract) (scrut : Scrutinee) {key : Key}
    (hr : scrutinee memory concrete scrut = some (key, next)) :
    ∃ after, evalScrutinee abstract scrut = some (key, after) ∧ EnvRep memory next after := by
  cases scrut with
  | value op =>
    cases ho : operand memory concrete op with
    | none => simp [scrutinee, ho] at hr
    | some pair =>
      rcases pair with ⟨cell, state⟩
      obtain ⟨value, after, hs, hv, he'⟩ := operand_reflect he op ho
      cases hv <;> simp only [scrutinee, ho, Bind.bind, Option.bind] at hr <;> try contradiction
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨after, by simp only [evalScrutinee, hs, Bind.bind, Option.bind], he'⟩
  | discriminant place =>
    cases hl : locate memory concrete place with
    | none => simp [scrutinee, hl] at hr
    | some pair =>
      rcases pair with ⟨cell, location⟩
      obtain ⟨value, hs, hv⟩ := locate_reflect he place hl
      cases hv <;> simp only [scrutinee, hl, Bind.bind, Option.bind] at hr <;> try contradiction
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨abstract, by simp only [evalScrutinee, hs, Bind.bind, Option.bind], he⟩

end SubtreeProofs.Rust.LookupSource.Heap
