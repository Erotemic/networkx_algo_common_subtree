module

public import SubtreeProofs.Rust.SourcePartialMoves
public import SubtreeProofs.Rust.LookupHeapOwnership

/-! Addressed partially initialized values over the existing heap cells. Cells
retain stored data after a move; the partial source value selects initialized
fields and complete ownership occurrences. Shared references own no addresses.
Representation alone does not assert allocation liveness or loan validity. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open LookupSource.Heap

mutual
  inductive Rep (memory : Memory) : Cell → Slot → List Nat → Prop where
    | empty (cell : Cell) : Rep memory cell .empty []
    | boolean (value : Bool) : Rep memory (.boolean value) (.boolean value) []
    | number (value : Nat) : Rep memory (.number value) (.number value) []
    | node {kind : Kind} {variant : Nat} {cells : List Cell} {parts : List Slot} {owners : List Nat} :
        FieldsRep memory cells parts owners → Rep memory (.node kind variant cells) (.node kind variant parts) owners
    | shared {pointer : Pointer} {target : Value} : Represents memory (.shared pointer) (.reference target) →
        Rep memory (.shared pointer) (.shared target) []
    | owned {address : Nat} {cell : Cell} {part : Slot} {owners : List Nat} :
        memory[address]? = some cell → Rep memory cell part owners →
        Rep memory (.owned address) (.boxed part) (owners ++ [address])

  inductive FieldsRep (memory : Memory) : List Cell → List Slot → List Nat → Prop where
    | nil : FieldsRep memory [] [] []
    | cons {cell : Cell} {part : Slot} {cells : List Cell} {parts : List Slot} {first rest : List Nat} :
        Rep memory cell part first → FieldsRep memory cells parts rest →
        FieldsRep memory (cell :: cells) (part :: parts) (first ++ rest)
end

mutual
  theorem Rep.mono {before after : Memory} (he : Extends before after)
      {cell : Cell} {part : Slot} {owners : List Nat} (h : Rep before cell part owners) : Rep after cell part owners :=
    match h with
    | .empty cell => .empty cell
    | .boolean b => .boolean b
    | .number n => .number n
    | .node fields => .node (fields.mono he)
    | .shared htarget => .shared (htarget.mono he)
    | .owned hr child => .owned (he _ _ hr) (child.mono he)

  theorem FieldsRep.mono {before after : Memory} (he : Extends before after)
      {cells : List Cell} {parts : List Slot} {owners : List Nat} (h : FieldsRep before cells parts owners) :
      FieldsRep after cells parts owners :=
    match h with
    | .nil => .nil
    | .cons first rest => .cons (first.mono he) (rest.mono he)
end

mutual
  theorem Rep.materialize {memory : Memory} {cell : Cell} {part : Slot} {owners : List Nat}
      (h : Rep memory cell part owners) {value : Value} (hm : part.materialize = some value) :
      Represents memory cell value ∧ Footprint memory cell owners := by
    cases h with
    | empty => simp only [Slot.materialize, reduceCtorEq] at hm
    | boolean b => simp only [Slot.materialize, Option.some.injEq] at hm; cases hm; exact ⟨.boolean b, .boolean b⟩
    | number n => simp only [Slot.materialize, Option.some.injEq] at hm; cases hm; exact ⟨.number n, .number n⟩
    | shared hv => simp only [Slot.materialize, Option.some.injEq] at hm; cases hm; exact ⟨hv, .shared _⟩
    | @owned address child part rest hr hc =>
      cases hp : part.materialize with
      | none => simp [Slot.materialize, hp] at hm
      | some inner =>
        simp only [Slot.materialize, hp, Functor.map, Option.map_some, Option.some.injEq] at hm
        subst value
        have hh := hc.materialize hp
        exact ⟨.owned hr hh.1, .owned hr hh.2⟩
    | @node kind variant cells parts rest hf =>
      cases hp : materializeFields parts with
      | none => simp [Slot.materialize, hp] at hm
      | some values =>
        simp only [Slot.materialize, hp, Functor.map, Option.map_some, Option.some.injEq] at hm
        subst value
        have hh := hf.materialize hp
        exact ⟨.node hh.1, .node hh.2⟩

  theorem FieldsRep.materialize {memory : Memory} {cells : List Cell} {parts : List Slot} {owners : List Nat}
      (h : FieldsRep memory cells parts owners) {values : List Value} (hm : materializeFields parts = some values) :
      RepresentsFields memory cells values ∧ FieldsFootprint memory cells owners := by
    cases h with
    | nil => simp only [materializeFields, Option.some.injEq] at hm; cases hm; exact ⟨.nil, .nil⟩
    | @cons cell part cells parts first rest hh ht =>
      cases hp : part.materialize with
      | none => simp [materializeFields, hp] at hm
      | some value =>
        cases hs : materializeFields parts with
        | none => simp [materializeFields, hp, hs] at hm
        | some tail =>
          simp only [materializeFields, hp, hs, bind, Option.bind, pure, Option.some.injEq] at hm
          subst values
          have hfirst := hh.materialize hp
          have hrest := ht.materialize hs
          exact ⟨.cons hfirst.1 hrest.1, .cons hfirst.2 hrest.2⟩
end

mutual
  theorem Rep.of_full {memory : Memory} {cell : Cell} {value : Value} {owners : List Nat}
      (hv : Represents memory cell value) (hf : Footprint memory cell owners) : Rep memory cell (Slot.ofValue value) owners := by
    cases hv with
    | boolean b => cases hf; simpa only [Slot.ofValue] using Rep.boolean (memory := memory) b
    | number n => cases hf; simpa only [Slot.ofValue] using Rep.number (memory := memory) n
    | node values => simpa only [Slot.ofValue] using Rep.node (FieldsRep.of_full values hf.node_inv)
    | shared hr child => cases hf; simpa only [Slot.ofValue] using Rep.shared (Represents.shared hr child)
    | owned hr child =>
      obtain ⟨rest, rfl, hp⟩ := hf.owned_inv hr
      simpa only [Slot.ofValue] using Rep.owned hr (Rep.of_full child hp)

  theorem FieldsRep.of_full {memory : Memory} {cells : List Cell} {values : List Value} {owners : List Nat}
      (hv : RepresentsFields memory cells values) (hf : FieldsFootprint memory cells owners) :
      FieldsRep memory cells (ofFields values) owners := by
    cases hv with
    | nil => cases hf; simpa only [ofFields] using FieldsRep.nil (memory := memory)
    | cons first rest =>
      obtain ⟨a, b, rfl, ha, hb⟩ := hf.cons_inv
      simpa only [ofFields] using FieldsRep.cons (Rep.of_full first ha) (FieldsRep.of_full rest hb)
end

mutual
  theorem Rep.boxes {memory : Memory} {cell : Cell} {part : Slot} {owners : List Nat}
      (h : Rep memory cell part owners) : owners.length = part.dropWork.boxes := by
    cases h with
    | empty | boolean _ | number _ | shared _ => simp only [Slot.dropWork, List.length_nil]
    | node fields => simpa only [Slot.dropWork, DropWork.plus, Nat.zero_add] using fields.boxes
    | owned _ child =>
      simp only [List.length_append, List.length_singleton, Slot.dropWork, DropWork.plus, child.boxes]
      omega

  theorem FieldsRep.boxes {memory : Memory} {cells : List Cell} {parts : List Slot} {owners : List Nat}
      (h : FieldsRep memory cells parts owners) : owners.length = (dropFields parts).boxes := by
    cases h with
    | nil => simp only [dropFields, List.length_nil]
    | cons first rest =>
      simp only [List.length_append, dropFields, DropWork.plus, first.boxes, rest.boxes]
end

mutual
  theorem Rep.bounds {memory : Memory} {cell : Cell} {part : Slot} {owners : List Nat}
      (h : Rep memory cell part owners) : ∀ address ∈ owners, address < memory.length :=
    match h with
    | .empty _ | .boolean _ | .number _ | .shared _ => by simp
    | .node fields => fields.bounds
    | .owned hr child => by
      intro address ha
      rcases List.mem_append.mp ha with ha | ha
      · exact child.bounds address ha
      · have hi := List.getElem?_eq_some_iff.mp hr |>.choose
        simpa only [List.mem_singleton.mp ha] using hi

  theorem FieldsRep.bounds {memory : Memory} {cells : List Cell} {parts : List Slot} {owners : List Nat}
      (h : FieldsRep memory cells parts owners) : ∀ address ∈ owners, address < memory.length :=
    match h with
    | .nil => by simp
    | .cons first rest => by
      intro address ha
      rcases List.mem_append.mp ha with ha | ha
      · exact first.bounds address ha
      · exact rest.bounds address ha
end


theorem Rep.alloc {memory : Memory} {cell : Cell} {part : Slot} {owners : List Nat}
    (h : Rep memory cell part owners) :
    Rep (Heap.alloc memory cell).2 (Heap.alloc memory cell).1 (.boxed part) (owners ++ [memory.length]) :=
  .owned (alloc_fresh memory cell).2.1 (h.mono (Extends.append memory [cell]))

end SubtreeProofs.Rust.LookupSource.Partial.Addressed
