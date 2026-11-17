module

public import SubtreeProofs.Rust.LookupTypedCode
public import SubtreeProofs.Rust.LookupHeapPrimitives

/-! Operational type preservation for successful immutable heap primitives.
Empty locals are permitted; initialization and exclusive ownership are separate
properties. Pointer reads are justified by the existing independent typing. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.SourceTypes

open Heap

mutual
  theorem typed_mono {before after : Memory} (he : Extends before after)
      {cell : Cell} {ty : Ty} (h : Typed before cell ty) : Typed after cell ty :=
    match h with
    | .boolean value => .boolean value
    | .number bound => .number bound
    | .node shape values => .node shape (fieldsTyped_mono he values)
    | .shared hr value => .shared (read_extends he hr) (typed_mono he value)
    | .owned hr value => .owned (he _ _ hr) (typed_mono he value)

  theorem fieldsTyped_mono {before after : Memory} (he : Extends before after)
      {cells : List Cell} {types : List Ty} (h : FieldsTyped before cells types) :
      FieldsTyped after cells types :=
    match h with
    | .nil => .nil
    | .cons first rest => .cons (typed_mono he first) (fieldsTyped_mono he rest)
end

def EnvTyped (memory : Memory) (locals : List Ty) (env : Locals) : Prop :=
  ∀ slot cell, env slot = some cell → ∃ ty, locals[slot]? = some ty ∧ Typed memory cell ty

theorem EnvTyped.get {memory : Memory} {locals : List Ty} {env : Locals}
    (h : EnvTyped memory locals env) {slot : Nat} {cell : Cell} {ty : Ty}
    (hc : env slot = some cell) (ht : locals[slot]? = some ty) : Typed memory cell ty := by
  obtain ⟨actual, ha, hv⟩ := h slot cell hc
  rw [ht] at ha
  cases ha
  exact hv

theorem EnvTyped.clear {memory : Memory} {locals : List Ty} {env : Locals}
    (h : EnvTyped memory locals env) (slot : Nat) : EnvTyped memory locals (env.set slot none) := by
  intro index cell hc
  by_cases hi : index = slot
  · simp [Locals.set, hi] at hc
  · exact h index cell (by simpa only [Locals.set, hi, ite_false] using hc)

theorem EnvTyped.store {memory : Memory} {locals : List Ty} {env : Locals}
    (h : EnvTyped memory locals env) {slot : Nat} {cell : Cell} {ty : Ty}
    (ht : locals[slot]? = some ty) (hv : Typed memory cell ty) :
    EnvTyped memory locals (env.set slot (some cell)) := by
  intro index value hc
  by_cases hi : index = slot
  · subst index
    simp only [Locals.set, ite_true, Option.some.injEq] at hc
    subst value
    exact ⟨ty, ht, hv⟩
  · exact h index value (by simpa only [Locals.set, hi, ite_false] using hc)

theorem EnvTyped.mono {before after : Memory} (he : Extends before after)
    {locals : List Ty} {env : Locals} (h : EnvTyped before locals env) : EnvTyped after locals env := by
  intro slot cell hc
  obtain ⟨ty, ht, hv⟩ := h slot cell hc
  exact ⟨ty, ht, typed_mono he hv⟩

theorem fieldsTyped_get {memory : Memory} {cells : List Cell} {types : List Ty}
    (h : FieldsTyped memory cells types) (index : Nat) {cell : Cell} {ty : Ty}
    (hc : cells[index]? = some cell) (ht : types[index]? = some ty) : Typed memory cell ty := by
  induction index generalizing cells types with
  | zero => cases h with
    | nil => cases hc
    | cons first rest => cases hc; cases ht; exact first
  | succ index ih => cases h with
    | nil => cases hc
    | cons first rest => exact ih rest hc ht

theorem projection_fields {kind : Kind} {actual index : Nat} {types : List Ty} {ty fieldTy : Ty}
    {variant : Option Nat} (hs : Shape kind actual types ty)
    (hg : variant.all (· = actual) = true) (ht : fieldType ty variant index = some fieldTy) :
    types[index]? = some fieldTy := by
  cases hs <;> cases variant <;> simp_all [fieldType, constructorFields]

theorem locate_typed {memory : Memory} {locals : List Ty} {env : Locals}
    (he : EnvTyped memory locals env) (place : Place) {ty : Ty} {cell : Cell} {address : Option Pointer}
    (ht : inferPlace locals place = some ty) (hr : locate memory env place = some (cell, address)) :
    Typed memory cell ty ∧ ∀ pointer, address = some pointer → read memory pointer = some cell := by
  induction place generalizing ty cell address with
  | «local» slot =>
    simp only [locate] at hr
    cases hc : env slot with
    | none => simp [hc] at hr
    | some value =>
      simp only [hc, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨he.get hc ht, by simp⟩
  | deref place ih =>
    simp only [inferPlace] at ht
    cases hs : inferPlace locals place with
    | none => simp [hs] at ht
    | some parentTy =>
      simp only [hs, bind, Option.bind] at ht
      simp only [locate] at hr
      cases hp : locate memory env place with
      | none => simp [hp] at hr
      | some pair =>
        rcases pair with ⟨parent, loc⟩
        obtain ⟨hv, _⟩ := ih hs hp
        cases hv with
        | boolean _ => cases ht
        | number _ => cases ht
        | node shape values => cases shape <;> cases ht
        | shared read child =>
          simp only [deref, Option.some.injEq] at ht
          subst ty
          simp only [hp, bind, Option.bind, read, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          exact ⟨child, by intro p h; cases h; exact read⟩
        | owned read child =>
          simp only [deref, Option.some.injEq] at ht
          subst ty
          simp only [hp, bind, Option.bind, read, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          exact ⟨child, by intro p h; cases h; simpa [Heap.read, fields] using read⟩
  | field place variant index ih =>
    simp only [inferPlace] at ht
    cases hs : inferPlace locals place with
    | none => simp [hs] at ht
    | some parentTy =>
      simp only [hs, bind, Option.bind] at ht
      simp only [locate] at hr
      cases hp : locate memory env place with
      | none => simp [hp] at hr
      | some pair =>
        rcases pair with ⟨parent, loc⟩
        obtain ⟨hv, haddr⟩ := ih hs hp
        simp only [hp, bind, Option.bind] at hr
        cases hv <;> simp only at hr <;> try contradiction
        rename_i kind actual cells types values shape
        split at hr
        next hg =>
          cases hc : cells[index]? with
          | none => simp [hc] at hr
          | some value =>
            simp only [hc, Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl⟩ := hr
            refine ⟨fieldsTyped_get values index hc (projection_fields shape hg ht), ?_⟩
            intro pointer ha
            cases loc with
            | none => simp at ha
            | some address =>
              simp only [Option.map_some, Option.some.injEq] at ha
              subst pointer
              rw [read_field (haddr address rfl)]
              exact hc
        next => contradiction

theorem operand_typed {memory : Memory} {locals : List Ty} {env env' : Locals}
    (he : EnvTyped memory locals env) (op : Operand) {ty : Ty} {cell : Cell}
    (ht : inferOperand locals op = some ty) (hr : operand memory env op = some (cell, env')) :
    Typed memory cell ty ∧ EnvTyped memory locals env' := by
  cases op with
  | move slot =>
    simp only [operand] at hr
    cases hc : env slot with
    | none => simp [hc] at hr
    | some value =>
      simp only [hc, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨he.get hc ht, he.clear slot⟩
  | boolean value => cases ht; cases hr; exact ⟨.boolean value, he⟩
  | copy place =>
    simp only [inferOperand] at ht
    cases hs : inferPlace locals place with
    | none => simp [hs] at ht
    | some actual =>
      simp only [hs, bind, Option.bind] at ht
      split at ht
      next hc =>
        cases ht
        simp only [operand] at hr
        cases hl : locate memory env place with
        | none => simp [hl] at hr
        | some pair =>
          rcases pair with ⟨value, address⟩
          have hv := (locate_typed he place hs hl).1
          simp only [hl, bind, Option.bind] at hr
          cases value <;> try contradiction
          all_goals
            simp only [Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl⟩ := hr
            exact ⟨hv, he⟩
      next => cases ht

theorem operands_typed {memory : Memory} {locals : List Ty} {env env' : Locals}
    (he : EnvTyped memory locals env) (args : List Operand) {types : List Ty} {cells : List Cell}
    (ht : inferOperands locals args = some types) (hr : operands memory args env = some (cells, env')) :
    FieldsTyped memory cells types ∧ EnvTyped memory locals env' := by
  induction args generalizing env env' types cells with
  | nil => cases ht; cases hr; exact ⟨.nil, he⟩
  | cons first rest ih =>
    simp only [inferOperands, List.mapM_cons] at ht
    change (do let ty ← inferOperand locals first; let types ← inferOperands locals rest; pure (ty :: types)) = some types at ht
    cases hf : inferOperand locals first with
    | none => simp [hf] at ht
    | some ty =>
      cases hs : inferOperands locals rest with
      | none => simp [hf, hs] at ht
      | some ts =>
        simp only [hf, hs, bind, Option.bind, pure, Option.some.injEq] at ht
        subst types
        simp only [operands] at hr
        cases hc : operand memory env first with
        | none => simp [hc] at hr
        | some pair =>
          rcases pair with ⟨cell, middle⟩
          cases hcs : operands memory rest middle with
          | none => simp [hc, hcs] at hr
          | some pair =>
            rcases pair with ⟨vs, final⟩
            simp only [hc, hcs, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl⟩ := hr
            obtain ⟨hv, he'⟩ := operand_typed he first hf hc
            obtain ⟨hvs, he''⟩ := ih he' hs hcs
            exact ⟨.cons hv hvs, he''⟩

theorem borrow_typed {memory : Memory} {locals : List Ty} {env : Locals}
    (he : EnvTyped memory locals env) (place : Place) {ty : Ty} {cell : Cell}
    (ht : inferPlace locals place = some ty) (hr : borrow memory env place = some cell) :
    Typed memory cell (.shared ty) := by
  unfold borrow at hr
  cases hl : locate memory env place with
  | none => simp [hl] at hr
  | some pair =>
    rcases pair with ⟨value, address⟩
    obtain ⟨hv, hp⟩ := locate_typed he place ht hl
    cases address with
    | none => simp [hl] at hr
    | some pointer =>
      simp only [hl, bind, Option.bind] at hr
      cases hr
      exact .shared (hp pointer rfl) hv

theorem rvalue_typed {memory : Memory} {locals : List Ty} {env env' : Locals}
    (he : EnvTyped memory locals env) (rhs : RValue) {ty : Ty} {cell : Cell}
    (ht : inferRValue locals rhs = some ty) (hr : rvalue memory env rhs = some (cell, env')) :
    Typed memory cell ty ∧ EnvTyped memory locals env' := by
  cases rhs with
  | use op => exact operand_typed he op ht hr
  | address place =>
    simp only [inferRValue] at ht
    cases hs : inferPlace locals place with
    | none => simp [hs] at ht
    | some inner =>
      simp only [hs, Functor.map, Option.map, Option.some.injEq] at ht
      subst ty
      simp only [rvalue] at hr
      cases hb : borrow memory env place with
      | none => simp [hb] at hr
      | some value =>
        simp only [hb, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ⟨borrow_typed he place hs hb, he⟩
  | aggregate kind variant args =>
    obtain ⟨types, hs, shape⟩ := aggregate_shape ht
    simp only [rvalue] at hr
    cases hc : operands memory args env with
    | none => simp [hc] at hr
    | some pair =>
      rcases pair with ⟨values, final⟩
      simp only [hc, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨hvs, he'⟩ := operands_typed he args hs hc
      exact ⟨.node shape hvs, he'⟩

theorem scrutinee_typed {memory : Memory} {locals : List Ty} {env env' : Locals}
    (he : EnvTyped memory locals env) (scrut : Scrutinee) {kind : Option Kind} {key : Key}
    (ht : scrutineeType locals scrut = some kind) (hr : scrutinee memory env scrut = some (key, env')) :
    EnvTyped memory locals env' := by
  cases scrut with
  | discriminant place =>
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
  | value op =>
    simp only [scrutineeType] at ht
    split at ht
    next hc =>
      obtain ⟨ty, ho, hb⟩ := sameResult_sound hc
      cases hb
      simp only [scrutinee] at hr
      cases hs : operand memory env op with
      | none => simp [hs] at hr
      | some pair =>
        rcases pair with ⟨value, final⟩
        obtain ⟨_, he'⟩ := operand_typed he op ho hs
        simp only [hs, bind, Option.bind] at hr
        cases value <;> try contradiction
        simp only [Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact he'
    next => cases ht

end SubtreeProofs.Rust.LookupSource.SourceTypes
