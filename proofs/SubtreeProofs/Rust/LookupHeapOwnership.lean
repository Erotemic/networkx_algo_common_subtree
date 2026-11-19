module

public import SubtreeProofs.Rust.LookupHeapInputs

/-! Exclusive postorder ownership regions. Shared pointers own no cells.
Each Box owns its payload interval followed by its own fresh cell; aggregate
fields receive adjacent, disjoint intervals. This is stronger than read-only
representation, which deliberately permits aliases. -/

@[expose] public section

register_simp_attr heap_layout_simps

namespace SubtreeProofs.Rust.LookupSource.Heap

mutual
  inductive Owns (memory : Memory) : Cell → Nat → Nat → Prop where
    | boolean (value : Bool) (start : Nat) : Owns memory (.boolean value) start start
    | number (value : Nat) (start : Nat) : Owns memory (.number value) start start
    | shared (pointer : Pointer) (start : Nat) : Owns memory (.shared pointer) start start
    | node {kind : Kind} {variant : Nat} {cells : List Cell} {start stop : Nat} :
        OwnsFields memory cells start stop → Owns memory (.node kind variant cells) start stop
    | owned {address start : Nat} {cell : Cell} :
        memory[address]? = some cell → Owns memory cell start address →
        Owns memory (.owned address) start (address + 1)

  inductive OwnsFields (memory : Memory) : List Cell → Nat → Nat → Prop where
    | nil (start : Nat) : OwnsFields memory [] start start
    | cons {cell : Cell} {cells : List Cell} {start middle stop : Nat} :
        Owns memory cell start middle → OwnsFields memory cells middle stop →
        OwnsFields memory (cell :: cells) start stop
end

mutual
  inductive Footprint (memory : Memory) : Cell → List Nat → Prop where
    | boolean (value : Bool) : Footprint memory (.boolean value) []
    | number (value : Nat) : Footprint memory (.number value) []
    | shared (pointer : Pointer) : Footprint memory (.shared pointer) []
    | node {kind : Kind} {variant : Nat} {cells : List Cell} {addresses : List Nat} :
        FieldsFootprint memory cells addresses → Footprint memory (.node kind variant cells) addresses
    | owned {address : Nat} {cell : Cell} {addresses : List Nat} :
        memory[address]? = some cell → Footprint memory cell addresses →
        Footprint memory (.owned address) (addresses ++ [address])

  inductive FieldsFootprint (memory : Memory) : List Cell → List Nat → Prop where
    | nil : FieldsFootprint memory [] []
    | cons {cell : Cell} {cells : List Cell} {first rest : List Nat} :
        Footprint memory cell first → FieldsFootprint memory cells rest →
        FieldsFootprint memory (cell :: cells) (first ++ rest)
end

mutual
  theorem Owns.bounds {memory : Memory} {cell : Cell} {start stop : Nat}
      (h : Owns memory cell start stop) : start ≤ stop :=
    match h with
    | .boolean _ _ | .number _ _ | .shared _ _ => le_refl _
    | .node hs => hs.bounds
    | .owned _ hs => Nat.le_trans hs.bounds (Nat.le_succ _)

  theorem OwnsFields.bounds {memory : Memory} {cells : List Cell} {start stop : Nat}
      (h : OwnsFields memory cells start stop) : start ≤ stop :=
    match h with
    | .nil _ => le_refl _
    | .cons h hs => h.bounds.trans hs.bounds
end

mutual
  theorem Owns.mono {before after : Memory} (he : Extends before after)
      {cell : Cell} {start stop : Nat} (h : Owns before cell start stop) :
      Owns after cell start stop :=
    match h with
    | .boolean value start => .boolean value start
    | .number value start => .number value start
    | .shared pointer start => .shared pointer start
    | .node hs => .node (hs.mono he)
    | .owned hr hs => .owned (he _ _ hr) (hs.mono he)

  theorem OwnsFields.mono {before after : Memory} (he : Extends before after)
      {cells : List Cell} {start stop : Nat} (h : OwnsFields before cells start stop) :
      OwnsFields after cells start stop :=
    match h with
    | .nil start => .nil start
    | .cons h hs => .cons (h.mono he) (hs.mono he)
end

mutual
  theorem Owns.footprint {memory : Memory} {cell : Cell} {start stop : Nat}
      (h : Owns memory cell start stop) : Footprint memory cell (List.range' start (stop - start)) := by
    cases h with
    | boolean value start => simpa using (Footprint.boolean (memory := memory) value)
    | number value start => simpa using (Footprint.number (memory := memory) value)
    | shared pointer start => simpa using (Footprint.shared (memory := memory) pointer)
    | node hs => exact .node hs.footprint
    | @owned address start cell hr hs =>
      have hle := hs.bounds
      have he : address + 1 - start = (address - start) + 1 := by omega
      rw [he, List.range'_1_concat, Nat.add_sub_of_le hle]
      exact .owned hr hs.footprint

  theorem OwnsFields.footprint {memory : Memory} {cells : List Cell} {start stop : Nat}
      (h : OwnsFields memory cells start stop) :
      FieldsFootprint memory cells (List.range' start (stop - start)) := by
    cases h with
    | nil start => simpa using (FieldsFootprint.nil (memory := memory))
    | @cons cell cells start middle stop hh ht =>
      have hle := hh.bounds
      have hle' := ht.bounds
      have he : (middle - start) + (stop - middle) = stop - start := by omega
      have hrange : List.range' start (middle - start) ++ List.range' middle (stop - middle) =
          List.range' start (stop - start) := by
        simpa only [Nat.add_sub_of_le hle, he] using
          (List.range'_append_1 (s := start) (m := middle - start) (n := stop - middle))
      rw [← hrange]
      exact .cons hh.footprint ht.footprint
end

theorem Footprint.node_inv {memory : Memory} {kind : Kind} {variant : Nat}
    {cells : List Cell} {addresses : List Nat}
    (h : Footprint memory (.node kind variant cells) addresses) : FieldsFootprint memory cells addresses := by
  cases h with | node h => exact h

theorem Footprint.owned_inv {memory : Memory} {address : Nat} {cell : Cell} {addresses : List Nat}
    (hr : memory[address]? = some cell) (h : Footprint memory (.owned address) addresses) :
    ∃ rest, addresses = rest ++ [address] ∧ Footprint memory cell rest := by
  cases h with
  | owned hr' ht =>
    have he := Option.some.inj (hr'.symm.trans hr)
    cases he
    exact ⟨_, rfl, ht⟩

theorem FieldsFootprint.cons_inv {memory : Memory} {cell : Cell} {cells : List Cell} {addresses : List Nat}
    (h : FieldsFootprint memory (cell :: cells) addresses) :
    ∃ first rest, addresses = first ++ rest ∧ Footprint memory cell first ∧ FieldsFootprint memory cells rest := by
  cases h with | cons h hs => exact ⟨_, _, rfl, h, hs⟩

mutual
  theorem Footprint.unique {memory : Memory} {cell : Cell} {first second : List Nat}
      (h₁ : Footprint memory cell first) (h₂ : Footprint memory cell second) : first = second :=
    match h₁ with
    | .boolean _ => by cases h₂; rfl
    | .number _ => by cases h₂; rfl
    | .shared _ => by cases h₂; rfl
    | .node hs => hs.unique h₂.node_inv
    | .owned hr hs => by
      obtain ⟨rest, he, ht⟩ := h₂.owned_inv hr
      rw [he, hs.unique ht]

  theorem FieldsFootprint.unique {memory : Memory} {cells : List Cell} {first second : List Nat}
      (h₁ : FieldsFootprint memory cells first) (h₂ : FieldsFootprint memory cells second) :
      first = second :=
    match h₁ with
    | .nil => by cases h₂; rfl
    | .cons hh hs => by
      obtain ⟨left, right, he, ht, hu⟩ := h₂.cons_inv
      rw [he, hh.unique ht, hs.unique hu]
end

/-- Every ownership occurrence is accounted for, exactly once, and belongs
to this interval. This rules out duplicated Box aliases and omitted cells. -/
theorem Owns.exclusive {memory : Memory} {cell : Cell} {start stop : Nat}
    (h : Owns memory cell start stop) {addresses : List Nat} (hf : Footprint memory cell addresses) :
    addresses = List.range' start (stop - start) ∧ addresses.Nodup ∧
      ∀ address, address ∈ addresses ↔ start ≤ address ∧ address < stop := by
  have he := hf.unique h.footprint
  refine ⟨he, he ▸ List.nodup_range', ?_⟩
  intro address
  rw [he, List.mem_range']
  simp only [Nat.one_mul]
  constructor
  · rintro ⟨index, hi, rfl⟩; omega
  · rintro ⟨hlo, hhi⟩
    exact ⟨address - start, by omega, by omega⟩

theorem alloc_owns {memory : Memory} {cell : Cell} {start : Nat}
    (h : Owns memory cell start memory.length) :
    Owns (alloc memory cell).2 (alloc memory cell).1 start (alloc memory cell).2.length := by
  have hr : Owns (memory ++ [cell]) (.owned memory.length) start (memory.length + 1) :=
    .owned (by simp) (h.mono (Extends.append memory [cell]))
  simpa [alloc] using hr

open verified_ordered_core in
theorem packWord_owns (word : BalancedWord) (memory : Memory) :
    Owns (packWord word memory).2 (packWord word memory).1 memory.length
      (packWord word memory).2.length := by
  induction word generalizing memory with
  | Empty => exact .node (.nil _)
  | Pair head tail ihHead ihTail =>
    have hh := ihHead memory
    have ht := ihTail (alloc (packWord head memory).2 (packWord head memory).1).2
    have he := (packWord_spec tail (alloc (packWord head memory).2 (packWord head memory).1).2).2
    have hhead := (alloc_owns hh).mono
      (he.trans (Extends.append
        (packWord tail (alloc (packWord head memory).2 (packWord head memory).1).2).2
        [(packWord tail (alloc (packWord head memory).2 (packWord head memory).1).2).1]))
    exact .node (.cons hhead (.cons (alloc_owns ht) (.nil _)))

open verified_ordered_core in
theorem packResult_owns (value : CommonEmbedding) (memory : Memory) :
    Owns (packResult value memory).2 (packResult value memory).1 memory.length
      (packResult value memory).2.length :=
  .node (.cons (packWord_owns value.word memory) (.cons (.number _ _) (.nil _)))

end SubtreeProofs.Rust.LookupSource.Heap
