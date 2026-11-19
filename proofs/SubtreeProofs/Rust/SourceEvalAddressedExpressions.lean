module

public import SubtreeProofs.Rust.SourceEvalAddressedOperands

/-! Syntax-directed addressed execution of all current RHS forms. Aggregates
assemble actual cells and their initialization metadata from operand packets;
comparisons inspect concrete numbers. Source correspondence is proved separately. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed Storage

def expression (world : World) (roots : Roots) (guarded : List Nat) (state : State) : Expr → Option (ValueCell × State)
  | .use op => operand world roots guarded state op
  | .address place => do
    let value ← state.read place
    let cell ← Storage.borrow world roots place
    some ((cell, .reference value), state)
  | .aggregate kind tag args => do
    let (cells, after) ← operands world roots guarded state args
    some ((.node kind tag (cells.map Prod.fst), .node kind tag (cells.map Prod.snd)), after)
  | .less left right => do
    let ((left, _), middle) ← operand world roots guarded state left
    let ((right, _), after) ← operand world roots guarded middle right
    match left, right with
    | .number left, .number right => do
      let answer ← less32 left right
      some ((.boolean answer, .boolean answer), after)
    | _, _ => none

theorem expression_spec {world : World} {frame : Nat} {roots : Roots} {state after : State} {guards guarded : List Nat}
    (hf : Frame world frame roots state guards) {rhs : Expr} {cell : Heap.Cell} {value : Value}
    (h : expression world roots guarded state rhs = some ((cell, value), after)) :
    ∃ used, SourceEval.expression state rhs = some (value, after) ∧ Graph world.memory cell value used ∧
      used ⊆ guards ∧ Frame world frame roots after guards := by
  cases rhs with
  | use op => exact operand_spec hf h
  | address place =>
    cases hr : state.read place with
    | none => simp [expression, hr] at h
    | some target =>
      obtain ⟨pointer, used, hb, hl, hu⟩ := hf.borrow place hr
      simp only [expression, hr, hb, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      obtain ⟨found, hp, hg⟩ := hl.valid
      exact ⟨used ++ [pointer.root], by simp only [SourceEval.expression, hr, Bind.bind, Option.bind],
        .shared hp hg, hu, hf⟩
  | aggregate kind tag args =>
    cases hr : operands world roots guarded state args with
    | none => simp [expression, hr] at h
    | some pair =>
      rcases pair with ⟨cells, next⟩
      simp only [expression, hr, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      obtain ⟨used, hs, hg, hu, hf'⟩ := operands_spec hf args hr
      exact ⟨used, by simp only [SourceEval.expression, hs, Bind.bind, Option.bind], .node hg, hu, hf'⟩
  | less left right =>
    cases hl : operand world roots guarded state left with
    | none => simp [expression, hl] at h
    | some pair =>
      rcases pair with ⟨⟨first, firstValue⟩, middle⟩
      cases hr : operand world roots guarded middle right with
      | none => simp [expression, hl, hr] at h
      | some pair =>
        rcases pair with ⟨⟨last, lastValue⟩, final⟩
        obtain ⟨_, hs, hg, _, hm⟩ := operand_spec hf hl
        obtain ⟨_, ht, hg', _, hf'⟩ := operand_spec hm hr
        cases hg with
        | boolean _ | node _ | shared _ _ | owned _ _ => simp [expression, hl, hr] at h
        | number first => cases hg' with
          | boolean _ | node _ | shared _ _ | owned _ _ => simp [expression, hl, hr] at h
          | number last =>
            cases hc : less32 first last with
            | none => simp [expression, hl, hr, hc] at h
            | some answer =>
              simp only [expression, hl, hr, hc, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
              exact ⟨[], by simp only [SourceEval.expression, hs, ht, hc, Bind.bind, Option.bind], .boolean answer, by simp, hf'⟩

theorem expression_readable {world : World} {frame : Nat} {roots : Roots} {state after : State} {guards guarded : List Nat}
    (hf : Frame world frame roots state guards) {rhs : Expr} {cell : Heap.Cell} {value : Value}
    (h : expression world roots guarded state rhs = some ((cell, value), after)) :
    SourceEval.expression state rhs = some (value, after) ∧ Readable world.memory world.live cell value ∧
      Frame world frame roots after guards := by
  obtain ⟨used, hs, hg, hu, hf'⟩ := expression_spec hf h
  exact ⟨hs, ⟨used, hg, fun a ha => hf.alive a (hu ha)⟩, hf'⟩

end SubtreeProofs.Rust.SourceEval.Addressed
