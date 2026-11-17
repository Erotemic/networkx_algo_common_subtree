module

public import SubtreeProofs.Rust.SourceEvalAddressedAssignments

/-! Reverse simulation for all operand/RHS syntax under independent physical
move-route permissions. The heap/root map is fixed during RHS evaluation, so
these conditions do not assume a successful addressed parent execution. Actual
caller/active-loan coverage and program-level route discharge remain separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed Storage

def Allowed (world : World) (roots : Roots) (guarded : List Nat) : Operand → Prop
  | .move place => ∀ cell pointer, Storage.locate world roots place = some (cell, pointer) → pointer.root ∉ guarded
  | _ => True

def AllowedExpr (world : World) (roots : Roots) (guarded : List Nat) : Expr → Prop
  | .use op => Allowed world roots guarded op
  | .address _ => True
  | .aggregate _ _ ops => ∀ op ∈ ops, Allowed world roots guarded op
  | .less left right => Allowed world roots guarded left ∧ Allowed world roots guarded right

theorem operand_complete {world : World} {frame : Nat} {roots : Roots} {state after : State} {guards guarded : List Nat}
    (hf : Frame world frame roots state guards) {op : Operand} {value : Value}
    (h : SourceEval.operand state op = some (value, after)) (ha : Allowed world roots guarded op) :
    ∃ cell, operand world roots guarded state op = some ((cell, value), after) := by
  cases op with
  | move place =>
    obtain ⟨cell, _, hr, _, _, _⟩ := operand_move_complete hf h ha
    exact ⟨cell, hr⟩
  | boolean b =>
    simp only [SourceEval.operand, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.boolean b, rfl⟩
  | number n =>
    by_cases hb : n < 2^32
    · simp only [SourceEval.operand, hb, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨.number n, by simp only [operand, hb, ↓reduceIte]⟩
    · simp only [SourceEval.operand, hb, ite_false, reduceCtorEq] at h
  | copy place =>
    obtain ⟨rfl, hs, _⟩ := SourceEval.copy_nonowning h
    obtain ⟨cell, pointer, used, hl, hg, _⟩ := hf.locate place hs
    cases hg with
    | boolean b =>
      exact ⟨.boolean b, by simp only [operand, read, hs, hl, copyCell, Bind.bind, Option.bind]⟩
    | number n =>
      by_cases hb : n < 2^32
      · exact ⟨.number n, by simp only [operand, read, hs, hl, copyCell, hb, ↓reduceIte, Bind.bind, Option.bind]⟩
      · simp only [SourceEval.operand, hs, hb, ite_false, Bind.bind, Option.bind, reduceCtorEq] at h
    | @shared target child inner used hread hchild =>
      exact ⟨.shared target, by simp only [operand, read, hs, hl, copyCell, Bind.bind, Option.bind]⟩
    | node _ | owned _ _ => simp only [SourceEval.operand, hs, Bind.bind, Option.bind, reduceCtorEq] at h

theorem operands_complete {world : World} {frame : Nat} {roots : Roots} {state after : State} {guards guarded : List Nat}
    (hf : Frame world frame roots state guards) (ops : List Operand) {values : List Value}
    (h : SourceEval.operands state ops = some (values, after)) (ha : ∀ op ∈ ops, Allowed world roots guarded op) :
    ∃ cells, operands world roots guarded state ops = some (cells, after) ∧ cells.map Prod.snd = values := by
  induction ops generalizing state values with
  | nil =>
    simp only [SourceEval.operands, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, rfl⟩
  | cons first rest ih =>
    cases hs : SourceEval.operand state first with
    | none => simp [SourceEval.operands, hs] at h
    | some pair =>
      rcases pair with ⟨value, middle⟩
      cases ht : SourceEval.operands middle rest with
      | none => simp [SourceEval.operands, hs, ht] at h
      | some pair =>
        rcases pair with ⟨tail, final⟩
        simp only [SourceEval.operands, hs, ht, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨cell, hc⟩ := operand_complete hf hs (ha first (by simp))
        obtain ⟨_, _, _, _, hm⟩ := operand_spec hf hc
        obtain ⟨cells, hr, he⟩ := ih hm ht (fun op hop => ha op (by simp [hop]))
        exact ⟨(cell, value) :: cells, by simp only [operands, hc, hr, Bind.bind, Option.bind],
          by simp only [List.map_cons, he]⟩

theorem expression_complete {world : World} {frame : Nat} {roots : Roots} {state after : State} {guards guarded : List Nat}
    (hf : Frame world frame roots state guards) {rhs : Expr} {value : Value}
    (h : SourceEval.expression state rhs = some (value, after)) (ha : AllowedExpr world roots guarded rhs) :
    ∃ cell, expression world roots guarded state rhs = some ((cell, value), after) := by
  cases rhs with
  | use op => exact operand_complete hf h ha
  | address place =>
    cases hs : state.read place with
    | none => simp [SourceEval.expression, hs] at h
    | some target =>
      simp only [SourceEval.expression, hs, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨pointer, _, hb, _, _⟩ := hf.borrow place hs
      exact ⟨.shared pointer, by simp only [expression, hs, hb, Bind.bind, Option.bind]⟩
  | aggregate kind tag ops =>
    cases hs : SourceEval.operands state ops with
    | none => simp [SourceEval.expression, hs] at h
    | some pair =>
      rcases pair with ⟨values, next⟩
      simp only [SourceEval.expression, hs, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨cells, hr, he⟩ := operands_complete hf ops hs ha
      exact ⟨.node kind tag (cells.map Prod.fst), by simp only [expression, hr, he, Bind.bind, Option.bind]⟩
  | less left right =>
    cases hs : SourceEval.operand state left with
    | none => simp [SourceEval.expression, hs] at h
    | some pair =>
      rcases pair with ⟨first, middle⟩
      cases ht : SourceEval.operand middle right with
      | none => simp [SourceEval.expression, hs, ht] at h
      | some pair =>
        rcases pair with ⟨last, final⟩
        cases first with
        | boolean _ | node _ _ _ | reference _ | boxed _ => simp [SourceEval.expression, hs, ht] at h
        | number first => cases last with
          | boolean _ | node _ _ _ | reference _ | boxed _ => simp [SourceEval.expression, hs, ht] at h
          | number last =>
            cases hb : less32 first last with
            | none => simp [SourceEval.expression, hs, ht, hb] at h
            | some answer =>
              simp only [SourceEval.expression, hs, ht, hb, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨a, hl⟩ := operand_complete hf hs ha.1
              obtain ⟨_, _, hg, _, hm⟩ := operand_spec hf hl
              obtain ⟨b, hr⟩ := operand_complete hm ht ha.2
              obtain ⟨_, _, hg', _, _⟩ := operand_spec hm hr
              cases hg with | number _ => cases hg' with | number _ =>
                exact ⟨.boolean answer, by simp only [expression, hl, hr, hb, Bind.bind, Option.bind]⟩

end SubtreeProofs.Rust.SourceEval.Addressed
