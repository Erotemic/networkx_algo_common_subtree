module

public import SubtreeProofs.Rust.SourcePartialHeapDrop

/-! Finite reference graphs include shared targets as well as owned payloads.
Their address lists are read resources, not ownership ledgers: shared aliases
and repeated addresses are allowed. Partial holes do not expose stale data. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open LookupSource.Heap

mutual
  inductive Graph (memory : Memory) : Cell → Value → List Nat → Prop where
    | boolean (b : Bool) : Graph memory (.boolean b) (.boolean b) []
    | number (n : Nat) : Graph memory (.number n) (.number n) []
    | node {kind : Kind} {tag : Nat} {cells : List Cell} {values : List Value} {guards : List Nat} :
        GraphFields memory cells values guards → Graph memory (.node kind tag cells) (.node kind tag values) guards
    | shared {pointer : Pointer} {cell : Cell} {value : Value} {guards : List Nat} :
        read memory pointer = some cell → Graph memory cell value guards →
        Graph memory (.shared pointer) (.reference value) (guards ++ [pointer.root])
    | owned {address : Nat} {cell : Cell} {value : Value} {guards : List Nat} :
        memory[address]? = some cell → Graph memory cell value guards →
        Graph memory (.owned address) (.boxed value) (guards ++ [address])

  inductive GraphFields (memory : Memory) : List Cell → List Value → List Nat → Prop where
    | nil : GraphFields memory [] [] []
    | cons {cell : Cell} {value : Value} {cells : List Cell} {values : List Value} {first rest : List Nat} :
        Graph memory cell value first → GraphFields memory cells values rest →
        GraphFields memory (cell :: cells) (value :: values) (first ++ rest)
end

mutual
  theorem Graph.represents {memory : Memory} {cell : Cell} {value : Value} {guards : List Nat}
      (h : Graph memory cell value guards) : Represents memory cell value :=
    match h with
    | .boolean b => .boolean b
    | .number n => .number n
    | .node fields => .node fields.represents
    | .shared hr child => .shared hr child.represents
    | .owned hr child => .owned hr child.represents

  theorem GraphFields.represents {memory : Memory} {cells : List Cell} {values : List Value} {guards : List Nat}
      (h : GraphFields memory cells values guards) : RepresentsFields memory cells values :=
    match h with
    | .nil => .nil
    | .cons first rest => .cons first.represents rest.represents
end

mutual
  theorem graph_of_represents {memory : Memory} {cell : Cell} {value : Value}
      (h : Represents memory cell value) : ∃ guards, Graph memory cell value guards := by
    cases h with
    | boolean b => exact ⟨[], .boolean b⟩
    | number n => exact ⟨[], .number n⟩
    | node fields => obtain ⟨guards, hg⟩ := graphFields_of_represents fields; exact ⟨guards, .node hg⟩
    | shared hr child => obtain ⟨guards, hg⟩ := graph_of_represents child; exact ⟨_, .shared hr hg⟩
    | owned hr child => obtain ⟨guards, hg⟩ := graph_of_represents child; exact ⟨_, .owned hr hg⟩

  theorem graphFields_of_represents {memory : Memory} {cells : List Cell} {values : List Value}
      (h : RepresentsFields memory cells values) : ∃ guards, GraphFields memory cells values guards := by
    cases h with
    | nil => exact ⟨[], .nil⟩
    | cons first rest =>
      obtain ⟨a, ha⟩ := graph_of_represents first
      obtain ⟨b, hb⟩ := graphFields_of_represents rest
      exact ⟨a ++ b, .cons ha hb⟩
end

mutual
  theorem Graph.mono {before after : Memory} (he : Extends before after)
      {cell : Cell} {value : Value} {guards : List Nat} (h : Graph before cell value guards) :
      Graph after cell value guards :=
    match h with
    | .boolean b => .boolean b
    | .number n => .number n
    | .node fields => .node (fields.mono he)
    | .shared hr child => .shared (read_extends he hr) (child.mono he)
    | .owned hr child => .owned (he _ _ hr) (child.mono he)

  theorem GraphFields.mono {before after : Memory} (he : Extends before after)
      {cells : List Cell} {values : List Value} {guards : List Nat} (h : GraphFields before cells values guards) :
      GraphFields after cells values guards :=
    match h with
    | .nil => .nil
    | .cons first rest => .cons (first.mono he) (rest.mono he)
end

mutual
  inductive PartialGraph (memory : Memory) : Cell → Slot → List Nat → Prop where
    | empty (cell : Cell) : PartialGraph memory cell .empty []
    | boolean (b : Bool) : PartialGraph memory (.boolean b) (.boolean b) []
    | number (n : Nat) : PartialGraph memory (.number n) (.number n) []
    | node {kind : Kind} {tag : Nat} {cells : List Cell} {parts : List Slot} {guards : List Nat} :
        PartialGraphFields memory cells parts guards → PartialGraph memory (.node kind tag cells) (.node kind tag parts) guards
    | shared {pointer : Pointer} {value : Value} {guards : List Nat} :
        Graph memory (.shared pointer) (.reference value) guards → PartialGraph memory (.shared pointer) (.shared value) guards
    | owned {address : Nat} {cell : Cell} {part : Slot} {guards : List Nat} :
        memory[address]? = some cell → PartialGraph memory cell part guards →
        PartialGraph memory (.owned address) (.boxed part) (guards ++ [address])

  inductive PartialGraphFields (memory : Memory) : List Cell → List Slot → List Nat → Prop where
    | nil : PartialGraphFields memory [] [] []
    | cons {cell : Cell} {part : Slot} {cells : List Cell} {parts : List Slot} {first rest : List Nat} :
        PartialGraph memory cell part first → PartialGraphFields memory cells parts rest →
        PartialGraphFields memory (cell :: cells) (part :: parts) (first ++ rest)
end

mutual
  theorem Graph.partial {memory : Memory} {cell : Cell} {value : Value} {guards : List Nat}
      (h : Graph memory cell value guards) : PartialGraph memory cell (Slot.ofValue value) guards := by
    cases h with
    | boolean b => simpa only [Slot.ofValue] using PartialGraph.boolean (memory := memory) b
    | number n => simpa only [Slot.ofValue] using PartialGraph.number (memory := memory) n
    | node fields => simpa only [Slot.ofValue] using PartialGraph.node fields.partial
    | shared hr child => simpa only [Slot.ofValue] using PartialGraph.shared (Graph.shared hr child)
    | owned hr child => simpa only [Slot.ofValue] using PartialGraph.owned hr child.partial

  theorem GraphFields.partial {memory : Memory} {cells : List Cell} {values : List Value} {guards : List Nat}
      (h : GraphFields memory cells values guards) : PartialGraphFields memory cells (ofFields values) guards := by
    cases h with
    | nil => simpa only [ofFields] using PartialGraphFields.nil (memory := memory)
    | cons first rest => simpa only [ofFields] using PartialGraphFields.cons first.partial rest.partial
end

mutual
  theorem PartialGraph.materialize {memory : Memory} {cell : Cell} {part : Slot} {guards : List Nat}
      (h : PartialGraph memory cell part guards) {value : Value} (hm : part.materialize = some value) :
      Graph memory cell value guards := by
    cases h with
    | empty => simp only [Slot.materialize, reduceCtorEq] at hm
    | boolean b => simp only [Slot.materialize, Option.some.injEq] at hm; cases hm; exact .boolean b
    | number n => simp only [Slot.materialize, Option.some.injEq] at hm; cases hm; exact .number n
    | shared hg => simp only [Slot.materialize, Option.some.injEq] at hm; cases hm; exact hg
    | @owned address cell part guards hr child =>
      cases hp : part.materialize with
      | none => simp [Slot.materialize, hp] at hm
      | some inner =>
        simp only [Slot.materialize, hp, Functor.map, Option.map_some, Option.some.injEq] at hm
        subst value
        exact .owned hr (child.materialize hp)
    | @node kind tag cells parts guards fields =>
      cases hp : materializeFields parts with
      | none => simp [Slot.materialize, hp] at hm
      | some values =>
        simp only [Slot.materialize, hp, Functor.map, Option.map_some, Option.some.injEq] at hm
        subst value
        exact .node (fields.materialize hp)

  theorem PartialGraphFields.materialize {memory : Memory} {cells : List Cell} {parts : List Slot} {guards : List Nat}
      (h : PartialGraphFields memory cells parts guards) {values : List Value} (hm : materializeFields parts = some values) :
      GraphFields memory cells values guards := by
    cases h with
    | nil => simp only [materializeFields, Option.some.injEq] at hm; cases hm; exact .nil
    | @cons cell part cells parts first rest hh ht =>
      cases hp : part.materialize with
      | none => simp [materializeFields, hp] at hm
      | some value =>
        cases hs : materializeFields parts with
        | none => simp [materializeFields, hp, hs] at hm
        | some remaining =>
          simp only [materializeFields, hp, hs, bind, Option.bind, pure, Option.some.injEq] at hm
          subst values
          exact .cons (hh.materialize hp) (ht.materialize hs)
end

mutual
  theorem PartialGraph.mono {before after : Memory} (he : Extends before after)
      {cell : Cell} {part : Slot} {guards : List Nat} (h : PartialGraph before cell part guards) :
      PartialGraph after cell part guards :=
    match h with
    | .empty cell => .empty cell
    | .boolean b => .boolean b
    | .number n => .number n
    | .node fields => .node (fields.mono he)
    | .shared hg => .shared (hg.mono he)
    | .owned hr child => .owned (he _ _ hr) (child.mono he)

  theorem PartialGraphFields.mono {before after : Memory} (he : Extends before after)
      {cells : List Cell} {parts : List Slot} {guards : List Nat} (h : PartialGraphFields before cells parts guards) :
      PartialGraphFields after cells parts guards :=
    match h with
    | .nil => .nil
    | .cons first rest => .cons (first.mono he) (rest.mono he)
end

mutual
  theorem Rep.graph {memory : Memory} {cell : Cell} {part : Slot} {owners : List Nat}
      (h : Rep memory cell part owners) : ∃ guards, PartialGraph memory cell part guards := by
    cases h with
    | empty cell => exact ⟨[], .empty cell⟩
    | boolean b => exact ⟨[], .boolean b⟩
    | number n => exact ⟨[], .number n⟩
    | shared hv => obtain ⟨guards, hg⟩ := graph_of_represents hv; exact ⟨guards, .shared hg⟩
    | node fields => obtain ⟨guards, hg⟩ := FieldsRep.graph fields; exact ⟨guards, .node hg⟩
    | owned hr child => obtain ⟨guards, hg⟩ := child.graph; exact ⟨_, .owned hr hg⟩

  theorem FieldsRep.graph {memory : Memory} {cells : List Cell} {parts : List Slot} {owners : List Nat}
      (h : FieldsRep memory cells parts owners) : ∃ guards, PartialGraphFields memory cells parts guards := by
    cases h with
    | nil => exact ⟨[], .nil⟩
    | cons first rest =>
      obtain ⟨a, ha⟩ := first.graph
      obtain ⟨b, hb⟩ := rest.graph
      exact ⟨a ++ b, .cons ha hb⟩
end

/-- Liveness-backed finite readback, including the complete transitive shared
graph. This does not assert exclusive ownership or borrow-checker acceptance. -/
def Readable (memory : Memory) (live : Live) (cell : Cell) (value : Value) : Prop :=
  ∃ guards, Graph memory cell value guards ∧ AliveOn live guards

theorem Readable.represents {memory : Memory} {live : Live} {cell : Cell} {value : Value}
    (h : Readable memory live cell value) : Represents memory cell value := h.choose_spec.1.represents

theorem Readable.retire {memory : Memory} {live : Live} {cell : Cell} {value : Value}
    {guards discarded : List Nat} (hg : Graph memory cell value guards) (hl : AliveOn live guards)
    (hs : ∀ address ∈ guards, address ∉ discarded) : Readable memory (retire live discarded) cell value :=
  ⟨guards, hg, retire_preserves hs hl⟩

def readLive (memory : Memory) (live : Live) (pointer : Pointer) : Option Cell :=
  if live pointer.root then read memory pointer else none

theorem readLive_retired (memory : Memory) (live : Live) (discarded : List Nat) (pointer : Pointer)
    (h : pointer.root ∈ discarded) : readLive memory (retire live discarded) pointer = none := by
  simp only [readLive, retire_member live h, Bool.false_eq_true, ↓reduceIte]

end SubtreeProofs.Rust.LookupSource.Partial.Addressed
