module

public import SubtreeProofs.Rust.LookupSpatialPrimitives

/-! Exact complete ownership-occurrence conservation for the existing helper
primitives. This strengthens separation transport with a permutation ledger;
shared copies add no owners and disposable locals lose no owners. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Owners

open Spatial

def Conserves (memory : Memory) (before after : List Cell) : Prop :=
  ∀ owners, FieldsFootprint memory before owners →
    ∃ result, FieldsFootprint memory after result ∧ result.Perm owners

theorem Conserves.refl (memory : Memory) (cells : List Cell) : Conserves memory cells cells :=
  fun owners ho => ⟨owners, ho, .rfl⟩

theorem Conserves.perm {memory : Memory} {before after : List Cell} (h : before.Perm after) :
    Conserves memory before after := fun _ ho => fieldsFootprint_perm h ho

theorem Conserves.trans {memory : Memory} {first middle last : List Cell}
    (h₁ : Conserves memory first middle) (h₂ : Conserves memory middle last) : Conserves memory first last := by
  intro owners ho
  obtain ⟨a, ha, hp⟩ := h₁ owners ho
  obtain ⟨b, hb, hq⟩ := h₂ a ha
  exact ⟨b, hb, hq.trans hp⟩

theorem Conserves.prefix {memory : Memory} {before after : List Cell} (h : Conserves memory before after)
    (leading : List Cell) : Conserves memory (leading ++ before) (leading ++ after) := by
  intro owners ho
  obtain ⟨a, b, rfl, ha, hb⟩ := fieldsFootprint_split leading ho
  obtain ⟨c, hc, hp⟩ := h b hb
  exact ⟨a ++ c, fieldsFootprint_append ha hc, hp.append_left a⟩

theorem Conserves.plain_cons {memory : Memory} {cell : Cell} (hp : Frame.Plain cell) (cells : List Cell) :
    Conserves memory cells (cell :: cells) := by
  intro owners ho
  exact ⟨owners, by simpa using FieldsFootprint.cons (hp.footprint memory) ho, .rfl⟩

theorem Conserves.erase_plain_fields {memory : Memory} {cells : List Cell} (hp : Frame.PlainFields cells) (rest : List Cell) :
    Conserves memory (cells ++ rest) rest := by
  intro owners ho
  obtain ⟨a, b, rfl, ha, hb⟩ := fieldsFootprint_split cells ho
  have he := ha.unique (hp.footprint memory)
  subst a
  exact ⟨b, hb, by simp⟩

theorem Conserves.pack {memory : Memory} (kind : Kind) (tag : Nat) (cells rest : List Cell) :
    Conserves memory (cells ++ rest) (.node kind tag cells :: rest) := by
  intro owners ho
  obtain ⟨a, b, rfl, ha, hb⟩ := fieldsFootprint_split cells ho
  exact ⟨a ++ b, .cons (.node ha) hb, .rfl⟩

theorem clear {memory : Memory} {count slot : Nat} {env : Locals} (hs : slot < count)
    (hd : Frame.Disposable (env slot)) : Conserves memory (values count env) (values count (env.set slot none)) := by
  have plain : Frame.PlainFields (env slot).toList := by
    cases hc : env slot with
    | none => exact .nil
    | some cell => exact .cons (by simpa only [hc, Frame.Disposable] using hd) .nil
  exact (Conserves.perm (values_split count env slot hs)).trans (Conserves.erase_plain_fields plain _)

theorem store {memory : Memory} {count slot : Nat} {env : Locals} (hs : slot < count)
    (hd : Frame.Disposable (env slot)) (cell : Cell) :
    Conserves memory (cell :: values count env) (values count (env.set slot (some cell))) := by
  have first := (clear (memory := memory) hs hd).prefix [cell]
  have last : Conserves memory (cell :: values count (env.set slot none)) (values count (env.set slot (some cell))) :=
    Conserves.perm (by simpa only [Option.toList_some, List.singleton_append] using
      (values_set_split count env slot hs (some cell)).symm)
  exact first.trans last

theorem returning {memory : Memory} {count : Nat} {env : Locals} {cell : Cell} (hs : 0 < count)
    (hc : env 0 = some cell) (hd : ∀ index, index ≠ 0 → Frame.Disposable (env index)) :
    Conserves memory (values count env) [cell] := by
  have plain := plain_values (count := count) (Frame.return_frame_disposable hd)
  have first := Conserves.perm (memory := memory) (values_move hs hc)
  have last := (Conserves.erase_plain_fields (memory := memory) plain []).prefix [cell]
  exact first.trans (by simpa only [List.append_nil, List.singleton_append] using last)

theorem operand {memory : Memory} {count : Nat} {env env' : Locals} (hb : Bounded count env)
    (op : Operand) {cell : Cell} (hr : Heap.operand memory env op = some (cell, env')) :
    Bounded count env' ∧ Conserves memory (values count env) (cell :: values count env') := by
  cases op with
  | move slot =>
    simp only [Heap.operand] at hr
    cases hc : env slot with
    | none => simp [hc] at hr
    | some value =>
      simp only [hc, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      have hs : slot < count := by
        by_contra hn
        have he := hb slot (by omega)
        rw [hc] at he
        cases he
      exact ⟨hb.clear slot, Conserves.perm (values_move hs hc)⟩
  | boolean value => cases hr; exact ⟨hb, Conserves.plain_cons (.boolean value) _⟩
  | copy place =>
    simp only [Heap.operand] at hr
    cases hl : locate memory env place with
    | none => simp [hl] at hr
    | some pair =>
      rcases pair with ⟨value, address⟩
      simp only [hl, Bind.bind, Option.bind] at hr
      cases value <;> try contradiction
      all_goals
        simp only [Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ⟨hb, Conserves.plain_cons (by constructor) _⟩

theorem operands {memory : Memory} {count : Nat} {env env' : Locals} (hb : Bounded count env)
    (args : List Operand) {cells : List Cell} (hr : Heap.operands memory args env = some (cells, env')) :
    Bounded count env' ∧ Conserves memory (values count env) (cells ++ values count env') := by
  induction args generalizing env env' cells with
  | nil => cases hr; exact ⟨hb, Conserves.refl _ _⟩
  | cons first rest ih =>
    cases hc : Heap.operand memory env first with
    | none => simp [Heap.operands, hc] at hr
    | some pair =>
      rcases pair with ⟨cell, middle⟩
      cases hcs : Heap.operands memory rest middle with
      | none => simp [Heap.operands, hc, hcs] at hr
      | some pair =>
        rcases pair with ⟨vs, final⟩
        simp only [Heap.operands, hc, hcs, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        obtain ⟨hb', ht⟩ := operand hb first hc
        obtain ⟨hb'', ht'⟩ := ih hb' hcs
        exact ⟨hb'', ht.trans (ht'.prefix [cell])⟩

theorem rvalue {memory : Memory} {count : Nat} {env env' : Locals} (hb : Bounded count env)
    (rhs : RValue) {cell : Cell} (hr : Heap.rvalue memory env rhs = some (cell, env')) :
    Bounded count env' ∧ Conserves memory (values count env) (cell :: values count env') := by
  cases rhs with
  | use op => exact operand hb op hr
  | address place =>
    cases hc : borrow memory env place with
    | none => simp [Heap.rvalue, hc] at hr
    | some value =>
      simp only [Heap.rvalue, hc, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨hb, Conserves.plain_cons (Frame.borrow_plain hc) _⟩
  | aggregate kind tag args =>
    cases hc : Heap.operands memory args env with
    | none => simp [Heap.rvalue, hc] at hr
    | some pair =>
      rcases pair with ⟨vs, final⟩
      simp only [Heap.rvalue, hc, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨hb', ht⟩ := operands hb args hc
      exact ⟨hb', ht.trans (Conserves.pack kind tag vs _)⟩

theorem scrutinee {memory : Memory} {count : Nat} {env env' : Locals} (hb : Bounded count env)
    (scrut : Scrutinee) {key : Key} (hr : Heap.scrutinee memory env scrut = some (key, env')) :
    Bounded count env' ∧ Conserves memory (values count env) (values count env') := by
  cases scrut with
  | discriminant place =>
    cases hl : locate memory env place with
    | none => simp [Heap.scrutinee, hl] at hr
    | some pair =>
      rcases pair with ⟨value, address⟩
      simp only [Heap.scrutinee, hl, Bind.bind, Option.bind] at hr
      cases value <;> try contradiction
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨hb, Conserves.refl _ _⟩
  | value op =>
    cases hc : Heap.operand memory env op with
    | none => simp [Heap.scrutinee, hc] at hr
    | some pair =>
      rcases pair with ⟨value, final⟩
      obtain ⟨hb', ht⟩ := operand hb op hc
      simp only [Heap.scrutinee, hc, Bind.bind, Option.bind] at hr
      cases value <;> try contradiction
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨hb', ht.trans (Conserves.erase_plain_fields (.cons (.boolean _) .nil) _)⟩

end SubtreeProofs.Rust.LookupSource.Heap.Owners
