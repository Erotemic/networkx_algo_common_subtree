module

public import SubtreeProofs.Rust.LookupFrameState

/-! Spatial ownership of simultaneous live values. Complete occurrence lists
count nested Box ownership; shared references carry no ownership. A caller's
live values can be retained as an arbitrary frame. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Spatial

mutual
  theorem footprint_mono {before after : Memory} (he : Extends before after)
      {cell : Cell} {addresses : List Nat} (h : Footprint before cell addresses) :
      Footprint after cell addresses :=
    match h with
    | .boolean value => .boolean value
    | .number value => .number value
    | .shared pointer => .shared pointer
    | .node values => .node (fieldsFootprint_mono he values)
    | .owned hr value => .owned (he _ _ hr) (footprint_mono he value)

  theorem fieldsFootprint_mono {before after : Memory} (he : Extends before after)
      {cells : List Cell} {addresses : List Nat} (h : FieldsFootprint before cells addresses) :
      FieldsFootprint after cells addresses :=
    match h with
    | .nil => .nil
    | .cons first rest => .cons (footprint_mono he first) (fieldsFootprint_mono he rest)
end

mutual
  theorem footprint_bounds {memory : Memory} {cell : Cell} {addresses : List Nat}
      (h : Footprint memory cell addresses) : ∀ address ∈ addresses, address < memory.length :=
    match h with
    | .boolean _ | .number _ | .shared _ => by simp
    | .node values => fieldsFootprint_bounds values
    | .owned hr value => by
      intro address ha
      rcases List.mem_append.mp ha with ha | ha
      · exact footprint_bounds value address ha
      · have hi := List.getElem?_eq_some_iff.mp hr |>.choose
        have he := List.mem_singleton.mp ha
        simpa only [he] using hi

  theorem fieldsFootprint_bounds {memory : Memory} {cells : List Cell} {addresses : List Nat}
      (h : FieldsFootprint memory cells addresses) : ∀ address ∈ addresses, address < memory.length :=
    match h with
    | .nil => by simp
    | .cons first rest => by
      intro address ha
      rcases List.mem_append.mp ha with ha | ha
      · exact footprint_bounds first address ha
      · exact fieldsFootprint_bounds rest address ha
end

theorem fieldsFootprint_append {memory : Memory} {first rest : List Cell} {a b : List Nat}
    (hf : FieldsFootprint memory first a) (hr : FieldsFootprint memory rest b) :
    FieldsFootprint memory (first ++ rest) (a ++ b) := by
  induction first generalizing a with
  | nil => cases hf; exact hr
  | cons cell cells ih =>
    obtain ⟨a, b, rfl, hc, hs⟩ := hf.cons_inv
    simpa only [List.cons_append, List.append_assoc] using FieldsFootprint.cons hc (ih hs)

theorem fieldsFootprint_split {memory : Memory} (first : List Cell) {rest : List Cell} {addresses : List Nat}
    (h : FieldsFootprint memory (first ++ rest) addresses) :
    ∃ a b, addresses = a ++ b ∧ FieldsFootprint memory first a ∧ FieldsFootprint memory rest b := by
  induction first generalizing addresses with
  | nil => exact ⟨[], addresses, rfl, .nil, h⟩
  | cons cell cells ih =>
    obtain ⟨a, other, rfl, hf, hr⟩ := h.cons_inv
    obtain ⟨b, c, rfl, hb, hc⟩ := ih hr
    exact ⟨a ++ b, c, by simp only [List.append_assoc], .cons hf hb, hc⟩

theorem fieldsFootprint_perm {memory : Memory} {first second : List Cell}
    (hp : first.Perm second) {addresses : List Nat} (h : FieldsFootprint memory first addresses) :
    ∃ other, FieldsFootprint memory second other ∧ other.Perm addresses := by
  induction hp generalizing addresses with
  | nil => cases h; exact ⟨[], .nil, .rfl⟩
  | cons cell hp ih =>
    obtain ⟨a, b, rfl, hf, hr⟩ := h.cons_inv
    obtain ⟨c, hc, hperm⟩ := ih hr
    exact ⟨a ++ c, .cons hf hc, hperm.append_left a⟩
  | swap first second rest =>
    obtain ⟨a, b, rfl, hf, hr⟩ := h.cons_inv
    obtain ⟨c, d, rfl, hs, ht⟩ := hr.cons_inv
    exact ⟨c ++ (a ++ d), .cons hs (.cons hf ht), List.perm_append_comm_assoc c a d⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨b, hb, hperm⟩ := ih₁ h
    obtain ⟨c, hc, hperm'⟩ := ih₂ hb
    exact ⟨c, hc, hperm'.trans hperm⟩

def Separated (memory : Memory) (cells : List Cell) : Prop :=
  ∃ addresses, FieldsFootprint memory cells addresses ∧ addresses.Nodup

theorem Separated.every_footprint {memory : Memory} {cells : List Cell} {addresses : List Nat}
    (h : Separated memory cells) (hf : FieldsFootprint memory cells addresses) : addresses.Nodup := by
  obtain ⟨actual, ha, hn⟩ := h
  have he := hf.unique ha
  simpa only [he] using hn

theorem Separated.perm {memory : Memory} {first second : List Cell}
    (h : Separated memory first) (hp : first.Perm second) : Separated memory second := by
  obtain ⟨addresses, hf, hn⟩ := h
  obtain ⟨other, ho, hperm⟩ := fieldsFootprint_perm hp hf
  exact ⟨other, ho, hperm.nodup_iff.mpr hn⟩

theorem Separated.mono {before after : Memory} (he : Extends before after) {cells : List Cell}
    (h : Separated before cells) : Separated after cells := by
  obtain ⟨addresses, hf, hn⟩ := h
  exact ⟨addresses, fieldsFootprint_mono he hf, hn⟩

theorem Separated.plain_cons {memory : Memory} {cell : Cell} {cells : List Cell} (hp : Frame.Plain cell) :
    Separated memory (cell :: cells) ↔ Separated memory cells := by
  constructor
  · rintro ⟨addresses, hf, hn⟩
    obtain ⟨a, b, rfl, hc, hs⟩ := hf.cons_inv
    have ha := hc.unique (hp.footprint memory)
    subst a
    exact ⟨b, hs, hn⟩
  · rintro ⟨addresses, hf, hn⟩
    exact ⟨addresses, .cons (hp.footprint memory) hf, hn⟩

theorem Separated.pack {memory : Memory} {kind : Kind} {variant : Nat} {fields rest : List Cell}
    (h : Separated memory (fields ++ rest)) : Separated memory (.node kind variant fields :: rest) := by
  obtain ⟨addresses, hf, hn⟩ := h
  obtain ⟨a, b, rfl, ha, hb⟩ := fieldsFootprint_split fields hf
  exact ⟨a ++ b, .cons (.node ha) hb, hn⟩

theorem Separated.plain_fields {memory : Memory} {cells frame : List Cell} (hp : Frame.PlainFields cells) :
    Separated memory (cells ++ frame) ↔ Separated memory frame := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
    cases hp with
    | cons hc hs => exact (Separated.plain_cons hc).trans (ih hs)

theorem Separated.alloc {memory : Memory} {cell : Cell} {frame : List Cell}
    (h : Separated memory (cell :: frame)) : Separated (Heap.alloc memory cell).2 ((Heap.alloc memory cell).1 :: frame) := by
  obtain ⟨addresses, hf, hn⟩ := h
  have hb := fieldsFootprint_bounds hf
  obtain ⟨a, b, rfl, ha, hframe⟩ := hf.cons_inv
  have he : Extends memory (Heap.alloc memory cell).2 := Extends.append memory [cell]
  refine ⟨(a ++ [memory.length]) ++ b,
    .cons (.owned (alloc_fresh memory cell).2.1 (footprint_mono he ha)) (fieldsFootprint_mono he hframe), ?_⟩
  have hp : ((a ++ [memory.length]) ++ b).Perm (memory.length :: (a ++ b)) := by
    simpa only [List.append_assoc, List.singleton_append] using
      (List.perm_middle (a := memory.length) (l₁ := a) (l₂ := b))
  apply hp.nodup_iff.mpr
  apply List.nodup_cons.mpr
  exact ⟨fun hm => Nat.lt_irrefl _ (hb _ hm), hn⟩

/-- All other live values are preserved by an ownership transfer. -/
def Transfers (memory : Memory) (before after : List Cell) : Prop :=
  ∀ frame, Separated memory (before ++ frame) → Separated memory (after ++ frame)

theorem Transfers.refl (memory : Memory) (cells : List Cell) : Transfers memory cells cells := fun _ h => h

theorem Transfers.perm {memory : Memory} {before after : List Cell} (hp : before.Perm after) :
    Transfers memory before after := fun frame h => h.perm (hp.append_right frame)

theorem Transfers.trans {memory : Memory} {first second third : List Cell}
    (h₁ : Transfers memory first second) (h₂ : Transfers memory second third) : Transfers memory first third :=
  fun frame h => h₂ frame (h₁ frame h)

theorem Transfers.prefix {memory : Memory} {before after : List Cell}
    (h : Transfers memory before after) (leading : List Cell) : Transfers memory (leading ++ before) (leading ++ after) := by
  intro frame hs
  have h₁ : Separated memory (before ++ (leading ++ frame)) :=
    hs.perm (by simpa only [List.append_assoc] using List.perm_append_comm_assoc leading before frame)
  have h₂ := h (leading ++ frame) h₁
  exact h₂.perm (by simpa only [List.append_assoc] using List.perm_append_comm_assoc after leading frame)

end SubtreeProofs.Rust.LookupSource.Heap.Spatial
