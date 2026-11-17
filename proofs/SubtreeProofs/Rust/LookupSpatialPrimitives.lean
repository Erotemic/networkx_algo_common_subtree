module

public import SubtreeProofs.Rust.LookupSpatialLocals
public import SubtreeProofs.Rust.LookupFramePrimitives

/-! Framed spatial ownership transfers for actual local moves, copies,
borrows and aggregate construction. Valid pointer reads remain checked by
the unchanged interpreter and independent operational typing. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Spatial

theorem plain_transfer {memory : Memory} {cell : Cell} (hp : Frame.Plain cell) (cells : List Cell) :
    Transfers memory cells (cell :: cells) := by
  intro frame h
  exact (Separated.plain_cons hp).mpr h

theorem operand_spatial {memory : Memory} {count : Nat} {env env' : Locals}
    (hb : Bounded count env) (op : Operand) {cell : Cell}
    (hr : operand memory env op = some (cell, env')) :
    Bounded count env' ∧ Transfers memory (values count env) (cell :: values count env') := by
  cases op with
  | move slot =>
    simp only [operand] at hr
    cases hc : env slot with
    | none => simp [hc] at hr
    | some value =>
      simp only [hc, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      have hs : slot < count := by
        by_contra hn
        have he := hb slot (Nat.le_of_not_gt hn)
        rw [hc] at he
        cases he
      exact ⟨hb.clear slot, Transfers.perm (values_move hs hc)⟩
  | boolean value => cases hr; exact ⟨hb, plain_transfer (.boolean value) _⟩
  | copy place =>
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
        exact ⟨hb, plain_transfer (by constructor) _⟩

theorem operands_spatial {memory : Memory} {count : Nat} {env env' : Locals}
    (hb : Bounded count env) (args : List Operand) {cells : List Cell}
    (hr : operands memory args env = some (cells, env')) :
    Bounded count env' ∧ Transfers memory (values count env) (cells ++ values count env') := by
  induction args generalizing env env' cells with
  | nil => cases hr; exact ⟨hb, Transfers.refl _ _⟩
  | cons first rest ih =>
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
        obtain ⟨hb', ht⟩ := operand_spatial hb first hc
        obtain ⟨hb'', ht'⟩ := ih hb' hcs
        exact ⟨hb'', ht.trans (ht'.prefix [cell])⟩

theorem rvalue_spatial {memory : Memory} {count : Nat} {env env' : Locals}
    (hb : Bounded count env) (rhs : RValue) {cell : Cell}
    (hr : rvalue memory env rhs = some (cell, env')) :
    Bounded count env' ∧ Transfers memory (values count env) (cell :: values count env') := by
  cases rhs with
  | use op => exact operand_spatial hb op hr
  | address place =>
    simp only [rvalue] at hr
    cases hc : borrow memory env place with
    | none => simp [hc] at hr
    | some value =>
      simp only [hc, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨hb, plain_transfer (Frame.borrow_plain hc) _⟩
  | aggregate kind variant args =>
    simp only [rvalue] at hr
    cases hc : operands memory args env with
    | none => simp [hc] at hr
    | some pair =>
      rcases pair with ⟨vs, final⟩
      simp only [hc, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨hb', ht⟩ := operands_spatial hb args hc
      refine ⟨hb', ?_⟩
      intro frame h
      apply Separated.pack (fields := vs) (rest := values count final ++ frame)
      simpa only [List.append_assoc] using ht frame h

theorem scrutinee_spatial {memory : Memory} {count : Nat} {env env' : Locals}
    (hb : Bounded count env) (scrut : Scrutinee) {key : Key}
    (hr : scrutinee memory env scrut = some (key, env')) :
    Bounded count env' ∧ Transfers memory (values count env) (values count env') := by
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
      exact ⟨hb, Transfers.refl _ _⟩
  | value op =>
    simp only [scrutinee] at hr
    cases hc : operand memory env op with
    | none => simp [hc] at hr
    | some pair =>
      rcases pair with ⟨value, final⟩
      obtain ⟨hb', ht⟩ := operand_spatial hb op hc
      simp only [hc, bind, Option.bind] at hr
      cases value <;> try contradiction
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      refine ⟨hb', fun frame h => ?_⟩
      exact (Separated.plain_cons (Frame.Plain.boolean _)).mp (ht frame h)

end SubtreeProofs.Rust.LookupSource.Heap.Spatial
