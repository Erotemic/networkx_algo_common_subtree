module

public import SubtreeProofs.Rust.LookupHeapExecution
public import SubtreeProofs.Rust.LookupHeapOwnership

/-! A conservative local ownership abstraction for frame safety. `false`
means that a value owns no Box, while `true` may contain owned data. An absent
slot is actually empty. This abstraction does not identify individual owners;
exclusive returned ownership is proved separately. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Frame

mutual
  inductive Plain : Cell → Prop where
    | boolean (value : Bool) : Plain (.boolean value)
    | number (value : Nat) : Plain (.number value)
    | shared (pointer : Pointer) : Plain (.shared pointer)
    | node {kind : Kind} {variant : Nat} {cells : List Cell} :
        PlainFields cells → Plain (.node kind variant cells)

  inductive PlainFields : List Cell → Prop where
    | nil : PlainFields []
    | cons {cell : Cell} {cells : List Cell} : Plain cell → PlainFields cells → PlainFields (cell :: cells)
end

mutual
  theorem Plain.footprint {cell : Cell} (h : Plain cell) (memory : Memory) : Footprint memory cell [] :=
    match h with
    | .boolean value => .boolean value
    | .number value => .number value
    | .shared pointer => .shared pointer
    | .node hs => .node (hs.footprint memory)

  theorem PlainFields.footprint {cells : List Cell} (h : PlainFields cells) (memory : Memory) :
      FieldsFootprint memory cells [] :=
    match h with
    | .nil => .nil
    | .cons h hs => .cons (h.footprint memory) (hs.footprint memory)
end

def Disposable : Option Cell → Prop
  | none => True
  | some cell => Plain cell

theorem disposable_no_owned {memory : Memory} {cell : Cell} {addresses : List Nat}
    (hd : Disposable (some cell)) (hf : Footprint memory cell addresses) : addresses = [] :=
  hf.unique (hd.footprint memory)

/-- Moving slot zero into the caller leaves no owned value to destroy in
the departing frame. This says nothing about stack layout or unwind paths. -/
theorem return_frame_disposable {env : Locals}
    (h : ∀ index, index ≠ 0 → Disposable (env index)) (index : Nat) :
    Disposable ((env.set 0 none) index) := by
  by_cases hi : index = 0
  · simp [Locals.set, hi, Disposable]
  · simpa [Locals.set, hi] using h index hi

abbrev State := List (Option Bool)

def lookup (state : State) (slot : Nat) : Option Bool := state[slot]?.join

def Matches (flag : Bool) (cell : Cell) : Prop := if flag then True else Plain cell

def StateRep (state : State) (env : Locals) : Prop :=
  ∀ index, Option.Rel Matches (lookup state index) (env index)

def canClear (state : State) (slot : Nat) : Bool := lookup state slot != some true

theorem StateRep.get {state : State} {env : Locals} (h : StateRep state env)
    {slot : Nat} {flag : Bool} {cell : Cell} (hs : lookup state slot = some flag)
    (hc : env slot = some cell) : Matches flag cell := by
  have hx := h slot
  rw [hs, hc] at hx
  cases hx with | some hm => exact hm

theorem StateRep.empty {state : State} {env : Locals} (h : StateRep state env)
    {slot : Nat} (hs : lookup state slot = none) : env slot = none := by
  have hx := h slot
  rw [hs] at hx
  cases hc : env slot with
  | none => rfl
  | some cell => rw [hc] at hx; cases hx

theorem StateRep.clear {state : State} {env : Locals} (h : StateRep state env)
    {slot : Nat} (hs : canClear state slot = true) : Disposable (env slot) := by
  cases hc : env slot with
  | none => trivial
  | some cell =>
    cases hf : lookup state slot with
    | none => have he := h.empty hf; rw [hc] at he; cases he
    | some flag =>
      cases flag with
      | false => exact h.get hf hc
      | true => simp [canClear, hf] at hs

theorem lookup_set (state : State) (slot : Nat) (flag : Option Bool)
    (hb : slot < state.length) (index : Nat) :
    lookup (state.set slot flag) index = if index = slot then flag else lookup state index := by
  by_cases hi : index = slot
  · subst index; simp [lookup, List.getElem?_set_self hb]
  · simp [lookup, hi]

theorem StateRep.set {state : State} {env : Locals} (h : StateRep state env)
    (slot : Nat) (hb : slot < state.length) {flag : Option Bool} {cell : Option Cell}
    (hm : Option.Rel Matches flag cell) : StateRep (state.set slot flag) (env.set slot cell) := by
  intro index
  rw [lookup_set state slot flag hb index]
  by_cases hi : index = slot
  · simpa [Locals.set, hi] using hm
  · simpa [Locals.set, hi] using h index

def initialState (count : Nat) (flags : List Bool) : State :=
  none :: flags.map some ++ List.replicate count none

def FieldsMatch : List Bool → List Cell → Prop
  | [], [] => True
  | flag :: flags, cell :: cells => Matches flag cell ∧ FieldsMatch flags cells
  | _, _ => False

theorem fieldsMatch_get {flags : List Bool} {cells : List Cell} (h : FieldsMatch flags cells) (index : Nat) :
    Option.Rel Matches (flags.map some)[index]?.join cells[index]? := by
  induction flags generalizing cells index with
  | nil => cases cells with
    | nil => exact .none
    | cons _ _ => cases h
  | cons flag flags ih => cases cells with
    | nil => cases h
    | cons cell cells => cases index with
      | zero => exact .some h.1
      | succ index => exact ih h.2 index

theorem initial_rep (count : Nat) {flags : List Bool} {cells : List Cell} (h : FieldsMatch flags cells) :
    StateRep (initialState count flags) (initialLocals cells) := by
  intro index
  cases index with
  | zero => exact .none
  | succ index =>
    have hg := fieldsMatch_get h index
    simp only [lookup, initialState]
    change Option.Rel Matches ((flags.map some ++ List.replicate count none)[index]?.join) cells[index]?
    by_cases hi : index < flags.length
    · rw [List.getElem?_append_left (l₁ := flags.map some) (by simpa using hi)]
      exact hg
    · have hn : (flags.map some)[index]? = none := List.getElem?_eq_none_iff.mpr (by simpa using Nat.le_of_not_gt hi)
      rw [hn] at hg
      rw [List.getElem?_append_right (l₁ := flags.map some) (by simpa using Nat.le_of_not_gt hi)]
      simp only [List.getElem?_replicate]
      split <;> exact hg

def arity : Function → Nat
  | .copyWord | .copyResult | .boxNew => 1
  | .compare => 2
  | .lookup => 3

def outputFlag (function : Function) : Bool := function != .compare

def inputFlags (function : Function) : List Bool := List.replicate (arity function) false

def ArgsMatch (function : Function) (cells : List Cell) : Prop :=
  cells.length = arity function ∧ (function = .boxNew ∨ FieldsMatch (inputFlags function) cells)

end SubtreeProofs.Rust.LookupSource.Heap.Frame
