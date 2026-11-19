module

public import SubtreeProofs.Rust.LookupFrameChecker

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Frame

theorem FieldsMatch.length {flags : List Bool} {cells : List Cell} (h : FieldsMatch flags cells) :
    cells.length = flags.length := by
  induction flags generalizing cells with
  | nil => cases cells with
    | nil => rfl
    | cons _ _ => cases h
  | cons flag flags ih => cases cells with
    | nil => cases h
    | cons cell cells => exact congrArg Nat.succ (ih h.2)

theorem FieldsMatch.plain {flags : List Bool} {cells : List Cell} (h : FieldsMatch flags cells)
    (hf : flags.any id = false) : PlainFields cells := by
  induction flags generalizing cells with
  | nil => cases cells with
    | nil => exact .nil
    | cons _ _ => cases h
  | cons flag flags ih => cases cells with
    | nil => cases h
    | cons cell cells =>
      cases flag with
      | true => simp at hf
      | false => exact .cons h.1 (ih h.2 (by simpa using hf))

theorem PlainFields.matches {cells : List Cell} (h : PlainFields cells) :
    FieldsMatch (List.replicate cells.length false) cells :=
  match h with
  | .nil => trivial
  | .cons h hs => ⟨h, hs.matches⟩

theorem profile_sound {function : Function} {flags : List Bool} {cells : List Cell}
    (h : FieldsMatch flags cells) (hs : callProfile function flags = true) : ArgsMatch function cells := by
  have hp := Bool.and_eq_true_iff.mp hs
  have hlen : flags.length = arity function := by simpa using hp.1
  have hcells := h.length.trans hlen
  refine ⟨hcells, ?_⟩
  by_cases hf : function = .boxNew
  · exact Or.inl hf
  · apply Or.inr
    have ha : flags.any id = false := by simpa [hf] using hp.2
    simpa only [inputFlags, ← hcells] using (h.plain ha).matches

theorem operand_sound {state next : State} {memory : Memory} {env env' : Locals}
    (he : StateRep state env) (op : Operand) {flag : Bool} {cell : Cell}
    (hs : inferOperand state op = some (flag, next))
    (hr : operand memory env op = some (cell, env')) :
    Matches flag cell ∧ StateRep next env' := by
  cases op with
  | move slot =>
    simp only [inferOperand] at hs
    split at hs
    next hb =>
      cases hf : lookup state slot with
      | none => simp [hf] at hs
      | some f =>
        simp only [hf, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        simp only [operand] at hr
        cases hc : env slot with
        | none => simp [hc] at hr
        | some value =>
          simp only [hc, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          exact ⟨he.get hf hc, he.set slot hb .none⟩
    next => cases hs
  | boolean value =>
    cases hs
    cases hr
    exact ⟨.boolean value, he⟩
  | copy place =>
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
        exact ⟨by constructor, he⟩

theorem operands_sound {state next : State} {memory : Memory} {env env' : Locals}
    (he : StateRep state env) (args : List Operand) {flags : List Bool} {cells : List Cell}
    (hs : inferOperands state args = some (flags, next))
    (hr : operands memory args env = some (cells, env')) :
    FieldsMatch flags cells ∧ StateRep next env' := by
  induction args generalizing state next env env' flags cells with
  | nil => cases hs; cases hr; exact ⟨trivial, he⟩
  | cons first rest ih =>
    simp only [inferOperands] at hs
    cases hf : inferOperand state first with
    | none => simp [hf] at hs
    | some pair =>
      rcases pair with ⟨flag, middle⟩
      cases ht : inferOperands middle rest with
      | none => simp [hf, ht] at hs
      | some pair =>
        rcases pair with ⟨fs, last⟩
        simp only [hf, ht, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        simp only [operands] at hr
        cases hc : operand memory env first with
        | none => simp [hc] at hr
        | some pair =>
          rcases pair with ⟨cell, localState⟩
          cases hcs : operands memory rest localState with
          | none => simp [hc, hcs] at hr
          | some pair =>
            rcases pair with ⟨vs, localLast⟩
            simp only [hc, hcs, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl⟩ := hr
            obtain ⟨hv, he'⟩ := operand_sound he first hf hc
            obtain ⟨hvs, he''⟩ := ih he' ht hcs
            exact ⟨⟨hv, hvs⟩, he''⟩

theorem borrow_plain {memory : Memory} {env : Locals} {place : Place} {cell : Cell}
    (hr : borrow memory env place = some cell) : Plain cell := by
  unfold borrow at hr
  cases hl : locate memory env place with
  | none => simp [hl] at hr
  | some pair =>
    rcases pair with ⟨value, address⟩
    cases address with
    | none => simp [hl] at hr
    | some pointer =>
      simp only [hl, bind, Option.bind] at hr
      cases hr
      exact .shared pointer

theorem rvalue_sound {state next : State} {memory : Memory} {env env' : Locals}
    (he : StateRep state env) (rhs : RValue) {flag : Bool} {cell : Cell}
    (hs : inferRValue state rhs = some (flag, next))
    (hr : rvalue memory env rhs = some (cell, env')) :
    Matches flag cell ∧ StateRep next env' := by
  cases rhs with
  | use op => exact operand_sound he op hs hr
  | address place =>
    cases hs
    simp only [rvalue] at hr
    cases hb : borrow memory env place with
    | none => simp [hb] at hr
    | some value =>
      simp only [hb, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨borrow_plain hb, he⟩
  | aggregate kind variant args =>
    simp only [inferRValue] at hs
    cases hf : inferOperands state args with
    | none => simp [hf] at hs
    | some pair =>
      rcases pair with ⟨flags, last⟩
      simp only [hf, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      simp only [rvalue] at hr
      cases hc : operands memory args env with
      | none => simp [hc] at hr
      | some pair =>
        rcases pair with ⟨values, localLast⟩
        simp only [hc, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        obtain ⟨hm, he'⟩ := operands_sound he args hf hc
        refine ⟨?_, he'⟩
        by_cases hk : kind = .tuple
        · simp only [hk, ite_true]
          cases ha : flags.any id with
          | true => trivial
          | false => exact Plain.node (hm.plain ha)
        · simp [hk, Matches]

theorem scrutinee_sound {state next : State} {memory : Memory} {env env' : Locals}
    (he : StateRep state env) (scrut : Scrutinee) {key : Key}
    (hs : inferScrutinee state scrut = some next)
    (hr : scrutinee memory env scrut = some (key, env')) : StateRep next env' := by
  cases scrut with
  | discriminant place =>
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
  | value op =>
    simp only [inferScrutinee] at hs
    cases hf : inferOperand state op with
    | none => simp [hf] at hs
    | some pair =>
      rcases pair with ⟨flag, last⟩
      cases flag with
      | true => simp [hf] at hs
      | false =>
        simp only [hf, bind, Option.bind, Bool.false_eq_true, ite_false, Option.some.injEq] at hs
        subst next
        simp only [scrutinee] at hr
        cases hc : operand memory env op with
        | none => simp [hc] at hr
        | some pair =>
          rcases pair with ⟨value, localLast⟩
          obtain ⟨_, he'⟩ := operand_sound he op hf hc
          simp only [hc, bind, Option.bind] at hr
          cases value <;> try contradiction
          simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          exact he'

end SubtreeProofs.Rust.LookupSource.Heap.Frame
