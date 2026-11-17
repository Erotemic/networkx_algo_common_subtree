module

public import SubtreeProofs.Rust.LookupBorrowPlaces

/-! Loan preservation through actual primitive evaluation, including moves,
aggregate temporaries and source-certified reborrows through shared roots. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Borrow

theorem operand_safe {base current : Memory} (hext : Extends base current) {locals : List Ty} {env env' : Locals}
    (he : EnvSafe base current locals env) (op : Operand) {ty : Ty} {cell : Cell}
    (ht : SourceTypes.inferOperand locals op = some ty) (hr : operand current env op = some (cell, env')) :
    Safe base current cell ty ∧ EnvSafe base current locals env' := by
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
    simp only [SourceTypes.inferOperand] at ht
    cases hs : SourceTypes.inferPlace locals place with
    | none => simp [hs] at ht
    | some actual =>
      simp only [hs, bind, Option.bind] at ht
      split at ht
      next =>
        cases ht
        simp only [operand] at hr
        cases hl : locate current env place with
        | none => simp [hl] at hr
        | some pair =>
          rcases pair with ⟨value, address⟩
          have hv := (locate_safe hext he place hs hl).1
          simp only [hl, bind, Option.bind] at hr
          cases value <;> try contradiction
          all_goals
            simp only [Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl⟩ := hr
            exact ⟨hv, he⟩
      next => cases ht

theorem operands_safe {base current : Memory} (hext : Extends base current) {locals : List Ty} {env env' : Locals}
    (he : EnvSafe base current locals env) (args : List Operand) {types : List Ty} {cells : List Cell}
    (ht : SourceTypes.inferOperands locals args = some types) (hr : operands current args env = some (cells, env')) :
    FieldsSafe base current cells types ∧ EnvSafe base current locals env' := by
  induction args generalizing env env' types cells with
  | nil => cases ht; cases hr; exact ⟨.nil, he⟩
  | cons first rest ih =>
    simp only [SourceTypes.inferOperands, List.mapM_cons] at ht
    change (do let ty ← SourceTypes.inferOperand locals first
               let types ← SourceTypes.inferOperands locals rest
               pure (ty :: types)) = some types at ht
    cases hf : SourceTypes.inferOperand locals first with
    | none => simp [hf] at ht
    | some ty =>
      cases hs : SourceTypes.inferOperands locals rest with
      | none => simp [hf, hs] at ht
      | some ts =>
        simp only [hf, hs, bind, Option.bind, pure, Option.some.injEq] at ht
        subst types
        simp only [operands] at hr
        cases hc : operand current env first with
        | none => simp [hc] at hr
        | some pair =>
          rcases pair with ⟨cell, middle⟩
          cases hcs : operands current rest middle with
          | none => simp [hc, hcs] at hr
          | some pair =>
            rcases pair with ⟨vs, final⟩
            simp only [hc, hcs, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl⟩ := hr
            obtain ⟨hv, he'⟩ := operand_safe hext he first hf hc
            obtain ⟨hvs, he''⟩ := ih he' hs hcs
            exact ⟨.cons hv hvs, he''⟩

theorem rvalue_safe {base current : Memory} (hext : Extends base current) {locals : List Ty} {env env' : Locals}
    (he : EnvSafe base current locals env) (rhs : RValue) {ty : Ty} {cell : Cell}
    (ht : SourceTypes.inferRValue locals rhs = some ty) (hroute : rvalueRoutes locals rhs = true)
    (hr : rvalue current env rhs = some (cell, env')) : Safe base current cell ty ∧ EnvSafe base current locals env' := by
  cases rhs with
  | use op => exact operand_safe hext he op ht hr
  | address place =>
    simp only [SourceTypes.inferRValue] at ht
    cases hs : SourceTypes.inferPlace locals place with
    | none => simp [hs] at ht
    | some inner =>
      simp only [hs, Functor.map, Option.map, Option.some.injEq] at ht
      subst ty
      simp only [rvalue] at hr
      cases hb : borrow current env place with
      | none => simp [hb] at hr
      | some value =>
        simp only [hb, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ⟨borrow_safe hext he place hs hroute hb, he⟩
  | aggregate kind variant args =>
    obtain ⟨types, hs, shape⟩ := SourceTypes.aggregate_shape ht
    simp only [rvalue] at hr
    cases hc : operands current args env with
    | none => simp [hc] at hr
    | some pair =>
      rcases pair with ⟨vs, final⟩
      simp only [hc, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨hvs, he'⟩ := operands_safe hext he args hs hc
      exact ⟨.node shape hvs, he'⟩

theorem scrutinee_safe {base current : Memory} (hext : Extends base current) {locals : List Ty} {env env' : Locals}
    (he : EnvSafe base current locals env) (scrut : Scrutinee) {kind : Option Kind} {key : Key}
    (ht : SourceTypes.scrutineeType locals scrut = some kind) (hr : scrutinee current env scrut = some (key, env')) :
    EnvSafe base current locals env' := by
  cases scrut with
  | discriminant place =>
    simp only [scrutinee] at hr
    cases hl : locate current env place with
    | none => simp [hl] at hr
    | some pair =>
      rcases pair with ⟨value, address⟩
      simp only [hl, bind, Option.bind] at hr
      cases value <;> try contradiction
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact he
  | value op =>
    simp only [SourceTypes.scrutineeType] at ht
    split at ht
    next hc =>
      obtain ⟨ty, ho, hb⟩ := SourceTypes.sameResult_sound hc
      cases hb
      simp only [scrutinee] at hr
      cases hs : operand current env op with
      | none => simp [hs] at hr
      | some pair =>
        rcases pair with ⟨value, final⟩
        obtain ⟨_, he'⟩ := operand_safe hext he op ho hs
        simp only [hs, bind, Option.bind] at hr
        cases value <;> try contradiction
        simp only [Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact he'
    next => cases ht

end SubtreeProofs.Rust.LookupSource.Heap.Borrow
