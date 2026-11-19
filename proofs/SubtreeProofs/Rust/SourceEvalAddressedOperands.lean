module

public import SubtreeProofs.Rust.SourceFrameMoves

/-! Executable addressed operands. Actual cells come from memory/projections;
value metadata comes from the same primitive initialization steps and supports
later destination masks. No complete source operand/expression run is called.
Protected-root coverage and ownership separation remain execution invariants. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed Storage

abbrev ValueCell := Heap.Cell × Value

def read (world : World) (roots : Roots) (state : State) (place : Place) : Option (ValueCell × Heap.Pointer) := do
  let value ← state.read place
  let (cell, pointer) ← Storage.locate world roots place
  some ((cell, value), pointer)

def copyCell : Heap.Cell → Option Heap.Cell
  | .boolean b => some (.boolean b)
  | .shared pointer => some (.shared pointer)
  | .number n => if n < 2^32 then some (.number n) else none
  | _ => none

def operand (world : World) (roots : Roots) (guarded : List Nat) (state : State) : Operand → Option (ValueCell × State)
  | .move place => do
    let (value, after) ← state.move place
    let (cell, pointer) ← Storage.locate world roots place
    if pointer.root ∈ guarded then none else some ((cell, value), after)
  | .copy place => do
    let ((cell, value), _) ← read world roots state place
    some ((← copyCell cell, value), state)
  | .boolean b => some ((.boolean b, .boolean b), state)
  | .number n => if n < 2^32 then some ((.number n, .number n), state) else none

theorem read_spec {world : World} {frame : Nat} {roots : Roots} {state : State} {guards : List Nat}
    (hf : Frame world frame roots state guards) {place : Place} {cell : Heap.Cell} {value : Value} {pointer : Heap.Pointer}
    (hr : read world roots state place = some ((cell, value), pointer)) :
    ∃ used, state.read place = some value ∧ Graph world.memory cell value used ∧
      used ++ [pointer.root] ⊆ guards := by
  unfold read at hr
  cases hs : state.read place with
  | none => simp [hs] at hr
  | some foundValue =>
    cases hl : Storage.locate world roots place with
    | none => simp [hs, hl] at hr
    | some pair =>
      rcases pair with ⟨found, address⟩
      simp only [hs, hl, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr
      obtain ⟨cell, pointer, used, hh, hg, hu⟩ := hf.locate place hs
      have he := Option.some.inj (hl.symm.trans hh)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ⟨used, rfl, hg, hu⟩

theorem operand_move_iff {world : World} {roots : Roots} {guarded : List Nat} {state after : State}
    {place : Place} {cell : Heap.Cell} {value : Value} :
    operand world roots guarded state (.move place) = some ((cell, value), after) ↔
      ∃ pointer, state.move place = some (value, after) ∧
        Storage.locate world roots place = some (cell, pointer) ∧ pointer.root ∉ guarded := by
  constructor
  · intro h
    simp only [operand] at h
    cases hm : state.move place with
    | none => simp [hm] at h
    | some result =>
      rcases result with ⟨foundValue, next⟩
      cases hl : Storage.locate world roots place with
      | none => simp [hm, hl] at h
      | some pair =>
        rcases pair with ⟨found, pointer⟩
        by_cases hg : pointer.root ∈ guarded
        · simp [hm, hl, hg] at h
        · simp only [hm, hl, Bind.bind, Option.bind, hg, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
          exact ⟨pointer, rfl, rfl, hg⟩
  · rintro ⟨pointer, hm, hl, hg⟩
    simp only [operand, hm, hl, Bind.bind, Option.bind, hg, ↓reduceIte]

theorem operand_spec {world : World} {frame : Nat} {roots : Roots} {state after : State} {guards guarded : List Nat}
    (hf : Frame world frame roots state guards) {op : Operand} {cell : Heap.Cell} {value : Value}
    (h : operand world roots guarded state op = some ((cell, value), after)) :
    ∃ used, SourceEval.operand state op = some (value, after) ∧ Graph world.memory cell value used ∧
      used ⊆ guards ∧ Frame world frame roots after guards := by
  cases op with
  | move place =>
    obtain ⟨pointer, hm, hl, _⟩ := operand_move_iff.mp h
    obtain ⟨found, address, used, hh, hg, hu⟩ := hf.locate place (Partial.Locals.move_spec hm).1
    have he := Option.some.inj (hl.symm.trans hh)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨used, hm, hg, fun _ ha => hu (List.mem_append_left _ ha), hf.move hm⟩
  | boolean b =>
    simp only [operand, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨[], rfl, .boolean b, by simp, hf⟩
  | number n =>
    by_cases hb : n < 2^32
    · simp only [operand, hb, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact ⟨[], by simp only [SourceEval.operand, hb, ↓reduceIte], .number n, by simp, hf⟩
    · simp only [operand, hb, ite_false, reduceCtorEq] at h
  | copy place =>
    cases hr : read world roots state place with
    | none => simp [operand, hr] at h
    | some pair =>
      rcases pair with ⟨⟨raw, snapshot⟩, pointer⟩
      obtain ⟨used, hs, hg, hu⟩ := read_spec hf hr
      have hsub : used ⊆ guards := fun _ ha => hu (List.mem_append_left _ ha)
      cases hg with
      | boolean b =>
        simp only [operand, hr, copyCell, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        exact ⟨[], by simp only [SourceEval.operand, hs, Bind.bind, Option.bind], .boolean b, hsub, hf⟩
      | number n =>
        by_cases hb : n < 2^32
        · simp only [operand, hr, copyCell, hb, ↓reduceIte, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
          exact ⟨[], by simp only [SourceEval.operand, hs, hb, ↓reduceIte, Bind.bind, Option.bind], .number n, hsub, hf⟩
        · simp only [operand, hr, copyCell, hb, ite_false, Bind.bind, Option.bind, reduceCtorEq] at h
      | shared ht child =>
        simp only [operand, hr, copyCell, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        exact ⟨_, by simp only [SourceEval.operand, hs, Bind.bind, Option.bind], .shared ht child, hsub, hf⟩
      | node _ | owned _ _ => simp [operand, hr, copyCell] at h

theorem operand_move_complete {world : World} {frame : Nat} {roots : Roots} {state after : State}
    {guards guarded : List Nat} (hf : Frame world frame roots state guards) {place : Place} {value : Value}
    (hm : state.move place = some (value, after))
    (hs : ∀ cell pointer, Storage.locate world roots place = some (cell, pointer) → pointer.root ∉ guarded) :
    ∃ cell used, operand world roots guarded state (.move place) = some ((cell, value), after) ∧
      Graph world.memory cell value used ∧ used ⊆ guards ∧ Frame world frame roots after guards := by
  obtain ⟨cell, pointer, used, hl, hg, hu⟩ := hf.locate place (Partial.Locals.move_spec hm).1
  exact ⟨cell, used, operand_move_iff.mpr ⟨pointer, hm, hl, hs cell pointer hl⟩,
    hg, fun _ ha => hu (List.mem_append_left _ ha), hf.move hm⟩

def operands (world : World) (roots : Roots) (guarded : List Nat) : State → List Operand → Option (List ValueCell × State)
  | state, [] => some ([], state)
  | state, first :: rest => do
    let (cell, middle) ← operand world roots guarded state first
    let (cells, after) ← operands world roots guarded middle rest
    some (cell :: cells, after)

theorem operands_spec {world : World} {frame : Nat} {roots : Roots} {state after : State} {guards guarded : List Nat}
    (hf : Frame world frame roots state guards) (ops : List Operand) {cells : List ValueCell}
    (h : operands world roots guarded state ops = some (cells, after)) :
    ∃ used, SourceEval.operands state ops = some (cells.map Prod.snd, after) ∧
      GraphFields world.memory (cells.map Prod.fst) (cells.map Prod.snd) used ∧
      used ⊆ guards ∧ Frame world frame roots after guards := by
  induction ops generalizing state cells with
  | nil =>
    simp only [operands, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, .nil, by simp, hf⟩
  | cons first rest ih =>
    cases ho : operand world roots guarded state first with
    | none => simp [operands, ho] at h
    | some pair =>
      rcases pair with ⟨⟨cell, value⟩, middle⟩
      cases hr : operands world roots guarded middle rest with
      | none => simp [operands, ho, hr] at h
      | some pair =>
        rcases pair with ⟨tail, final⟩
        simp only [operands, ho, hr, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨a, hs, hg, ha, hm⟩ := operand_spec hf ho
        obtain ⟨b, ht, hg', hb, hf'⟩ := ih hm hr
        refine ⟨a ++ b, ?_, ?_, ?_, hf'⟩
        · simp only [SourceEval.operands, hs, ht, List.map_cons, Bind.bind, Option.bind]
        · simpa only [List.map_cons] using GraphFields.cons hg hg'
        · intro address hd
          rcases List.mem_append.mp hd with hd | hd
          · exact ha hd
          · exact hb hd

end SubtreeProofs.Rust.SourceEval.Addressed
