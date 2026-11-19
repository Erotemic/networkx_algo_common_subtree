module

public import SubtreeProofs.Rust.LookupSource

/-! Addressed memory for the read-only lookup fragment. Shared pointers name
stable heap cells and inline field paths; Box values name separately allocated
cells. No stack address, mutation, free or allocator failure is modeled here.
The representation relation is finite, so dangling/cyclic pointers cannot
represent a snapshot. Shared aliases are allowed; unique Box ownership is a
separate obligation, not inferred from this relation. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap

structure Pointer where
  root : Nat
  path : List Nat := []
  deriving DecidableEq, Repr

inductive Cell where
  | boolean : Bool → Cell
  | number : Nat → Cell
  | node : Kind → Nat → List Cell → Cell
  | shared : Pointer → Cell
  | owned : Nat → Cell
  deriving Repr

abbrev Memory := List Cell

def fields : Cell → List Nat → Option Cell
  | value, [] => some value
  | .node _ _ values, index :: rest => do fields (← values[index]?) rest
  | _, _ :: _ => none

def read (memory : Memory) (pointer : Pointer) : Option Cell := do
  fields (← memory[pointer.root]?) pointer.path

def Pointer.field (pointer : Pointer) (index : Nat) : Pointer :=
  ⟨pointer.root, pointer.path ++ [index]⟩

def Extends (before after : Memory) : Prop :=
  ∀ (index : Nat) (value : Cell), before[index]? = some value → after[index]? = some value

theorem Extends.refl (memory : Memory) : Extends memory memory := fun _ _ h => h

theorem Extends.trans {first second third : Memory}
    (h₁ : Extends first second) (h₂ : Extends second third) : Extends first third :=
  fun index value h => h₂ index value (h₁ index value h)

theorem Extends.append (memory suffix : Memory) : Extends memory (memory ++ suffix) := by
  intro index value h
  have hi : index < memory.length := List.getElem?_eq_some_iff.mp h |>.choose
  simpa only [List.getElem?_append_left hi] using h

theorem Extends.eq_of_length {before after : Memory} (he : Extends before after)
    (hlen : after.length = before.length) : after = before := by
  apply List.ext_getElem?
  intro index
  cases hs : before[index]? with
  | some cell => exact he index cell hs
  | none =>
    have hi := List.getElem?_eq_none_iff.mp hs
    exact List.getElem?_eq_none_iff.mpr (by omega)

theorem read_extends {before after : Memory} (he : Extends before after)
    {pointer : Pointer} {value : Cell} (hr : read before pointer = some value) :
    read after pointer = some value := by
  unfold read at hr ⊢
  cases hc : before[pointer.root]? with
  | none => simp [hc] at hr
  | some cell =>
    simp only [hc, bind, Option.bind] at hr
    simpa only [he _ _ hc, bind, Option.bind] using hr

theorem fields_append (value : Cell) (first rest : List Nat) :
    fields value (first ++ rest) = (fields value first).bind (fields · rest) := by
  induction first generalizing value with
  | nil => rfl
  | cons index first ih =>
    cases value <;> simp only [List.cons_append, fields, bind, Option.bind]
    rename_i kind variant values
    cases h : values[index]? <;> simp [ih, Option.bind]

theorem read_field {memory : Memory} {pointer : Pointer} {kind : Kind}
    {variant index : Nat} {values : List Cell}
    (hr : read memory pointer = some (.node kind variant values)) :
    read memory (pointer.field index) = values[index]? := by
  unfold read at hr ⊢
  cases hc : memory[pointer.root]? with
  | none => simp [hc] at hr
  | some cell =>
    simp only [hc, bind, Option.bind] at hr
    simp only [Pointer.field, hc, bind, Option.bind, fields_append, hr, fields]
    cases values[index]? <;> rfl

mutual
  inductive Represents (memory : Memory) : Cell → Value → Prop where
    | boolean (value : Bool) : Represents memory (.boolean value) (.boolean value)
    | number (value : Nat) : Represents memory (.number value) (.number value)
    | node {kind : Kind} {variant : Nat} {cells : List Cell} {values : List Value} :
        RepresentsFields memory cells values →
        Represents memory (.node kind variant cells) (.node kind variant values)
    | shared {pointer : Pointer} {cell : Cell} {value : Value} :
        read memory pointer = some cell → Represents memory cell value →
        Represents memory (.shared pointer) (.reference value)
    | owned {address : Nat} {cell : Cell} {value : Value} :
        memory[address]? = some cell → Represents memory cell value →
        Represents memory (.owned address) (.boxed value)

  inductive RepresentsFields (memory : Memory) : List Cell → List Value → Prop where
    | nil : RepresentsFields memory [] []
    | cons {cell : Cell} {value : Value} {cells : List Cell} {values : List Value} :
        Represents memory cell value → RepresentsFields memory cells values →
        RepresentsFields memory (cell :: cells) (value :: values)
end

mutual
  theorem Represents.mono {before after : Memory} (he : Extends before after)
      {cell : Cell} {value : Value} (h : Represents before cell value) :
      Represents after cell value :=
    match h with
    | .boolean value => .boolean value
    | .number value => .number value
    | .node values => .node (RepresentsFields.mono he values)
    | .shared hr value => .shared (read_extends he hr) (value.mono he)
    | .owned hr value => .owned (he _ _ hr) (value.mono he)

  theorem RepresentsFields.mono {before after : Memory} (he : Extends before after)
      {cells : List Cell} {values : List Value} (h : RepresentsFields before cells values) :
      RepresentsFields after cells values :=
    match h with
    | .nil => .nil
    | .cons first rest => .cons (first.mono he) (rest.mono he)
end

theorem RepresentsFields.get {memory : Memory} {cells : List Cell} {values : List Value}
    (h : RepresentsFields memory cells values) (index : Nat) :
    Option.Rel (Represents memory) cells[index]? values[index]? := by
  induction index generalizing cells values with
  | zero => cases h with
    | nil => exact .none
    | cons head _ => exact .some head
  | succ index ih => cases h with
    | nil => exact .none
    | cons _ tail => exact ih tail

abbrev Locals := Nat → Option Cell

def Locals.set (env : Locals) (slot : Nat) (value : Option Cell) : Locals :=
  fun index => if index = slot then value else env index

def EnvRep (memory : Memory) (concrete : Locals) (abstract : Env) : Prop :=
  ∀ index, Option.Rel (Represents memory) (concrete index) (abstract index)

theorem EnvRep.set {memory : Memory} {concrete : Locals} {abstract : Env}
    (h : EnvRep memory concrete abstract) (slot : Nat) {cell : Option Cell} {value : Option Value}
    (hv : Option.Rel (Represents memory) cell value) :
    EnvRep memory (concrete.set slot cell) (abstract.set slot value) := by
  intro index
  by_cases hi : index = slot <;> simp only [Locals.set, Env.set, hi, ite_true, ite_false]
  · exact hv
  · exact h index

theorem EnvRep.mono {before after : Memory} (he : Extends before after)
    {concrete : Locals} {abstract : Env} (h : EnvRep before concrete abstract) :
    EnvRep after concrete abstract := by
  intro index
  have hx := h index
  generalize concrete index = cell at hx ⊢
  generalize abstract index = value at hx ⊢
  cases hx with
  | none => exact .none
  | some hv => exact .some (hv.mono he)

def alloc (memory : Memory) (value : Cell) : Cell × Memory :=
  (.owned memory.length, memory ++ [value])

theorem alloc_fresh (memory : Memory) (value : Cell) :
    memory[memory.length]? = none ∧ (alloc memory value).2[memory.length]? = some value ∧
      (alloc memory value).2.length = memory.length + 1 := by
  simp [alloc]

theorem alloc_rep {memory : Memory} {cell : Cell} {value : Value}
    (h : Represents memory cell value) :
    Represents (alloc memory cell).2 (alloc memory cell).1 (.boxed value) := by
  apply Represents.owned (alloc_fresh memory cell).2.1
  exact h.mono (Extends.append memory [cell])

end SubtreeProofs.Rust.LookupSource.Heap
