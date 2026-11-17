module

public import SubtreeProofs.Rust.LookupSpatialOwnership

/-! Enumerating every live local and moving its complete ownership into or
out of the temporary bundle. No set-based erasure of duplicate owners is used. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Spatial

def tail (env : Locals) : Locals := fun index => env (index + 1)

def values : Nat → Locals → List Cell
  | 0, _ => []
  | count + 1, env => (env 0).toList ++ values count (tail env)

def Bounded (count : Nat) (env : Locals) : Prop := ∀ index, count ≤ index → env index = none

theorem mem_values (count : Nat) (env : Locals) (cell : Cell) :
    cell ∈ values count env ↔ ∃ slot, slot < count ∧ env slot = some cell := by
  induction count generalizing env with
  | zero => simp [values]
  | succ count ih =>
    simp only [values, List.mem_append, Option.mem_toList, ih]
    constructor
    · rintro (hc | ⟨slot, hs, hc⟩)
      · exact ⟨0, by omega, hc⟩
      · exact ⟨slot + 1, by omega, hc⟩
    · rintro ⟨slot, hs, hc⟩
      cases slot with
      | zero => exact Or.inl hc
      | succ slot => exact Or.inr ⟨slot, by omega, hc⟩

theorem values_covers {count slot : Nat} {env : Locals} {cell : Cell}
    (hb : Bounded count env) (hc : env slot = some cell) : cell ∈ values count env := by
  apply (mem_values count env cell).mpr
  have hs : slot < count := by
    by_contra hn
    have he := hb slot (Nat.le_of_not_gt hn)
    rw [hc] at he
    cases he
  exact ⟨slot, hs, hc⟩

theorem Bounded.clear {count : Nat} {env : Locals} (h : Bounded count env) (slot : Nat) :
    Bounded count (env.set slot none) := by
  intro index hi
  by_cases hs : index = slot <;> simp [Locals.set, hs, h index hi]

theorem Bounded.store {count slot : Nat} {env : Locals} (h : Bounded count env)
    (hs : slot < count) (value : Option Cell) : Bounded count (env.set slot value) := by
  intro index hi
  have hn : index ≠ slot := by omega
  simp [Locals.set, hn, h index hi]

theorem tail_set_zero (env : Locals) (value : Option Cell) : tail (env.set 0 value) = tail env := by
  funext index
  simp [tail, Locals.set]

theorem tail_set_succ (env : Locals) (slot : Nat) (value : Option Cell) :
    tail (env.set (slot + 1) value) = (tail env).set slot value := by
  funext index
  simp [tail, Locals.set]

theorem clear_store (env : Locals) (slot : Nat) (value : Option Cell) :
    (env.set slot value).set slot none = env.set slot none := by
  funext index
  by_cases hi : index = slot <;> simp [Locals.set, hi]

theorem values_split (count : Nat) (env : Locals) (slot : Nat) (hs : slot < count) :
    (values count env).Perm ((env slot).toList ++ values count (env.set slot none)) := by
  induction count generalizing env slot with
  | zero => omega
  | succ count ih =>
    cases slot with
    | zero => simp only [values, Locals.set, ite_true, Option.toList_none, List.nil_append, tail_set_zero]; exact .rfl
    | succ slot =>
      have hb : slot < count := by omega
      have hi := ih (tail env) slot hb
      simp only [values, Locals.set, tail_set_succ]
      exact (hi.append_left (env 0).toList).trans (List.perm_append_comm_assoc _ _ _)

theorem values_set_split (count : Nat) (env : Locals) (slot : Nat) (hs : slot < count) (value : Option Cell) :
    (values count (env.set slot value)).Perm (value.toList ++ values count (env.set slot none)) := by
  have hp := values_split count (env.set slot value) slot hs
  simpa only [Locals.set, ite_true, clear_store] using hp

theorem values_move {count slot : Nat} {env : Locals} {cell : Cell} (hs : slot < count)
    (hc : env slot = some cell) :
    (values count env).Perm (cell :: values count (env.set slot none)) := by
  simpa only [hc, Option.toList_some, List.singleton_append] using values_split count env slot hs

theorem clear_transfer {count slot : Nat} {env : Locals} (hs : slot < count) (hd : Frame.Disposable (env slot)) :
    Transfers memory (values count env) (values count (env.set slot none)) := by
  intro frame h
  have h' := h.perm ((values_split count env slot hs).append_right frame)
  cases hc : env slot with
  | none => simpa only [hc, Option.toList_none, List.nil_append] using h'
  | some cell =>
    simp only [hc, Option.toList_some, List.cons_append] at h'
    exact (Separated.plain_cons (by simpa only [hc, Frame.Disposable] using hd)).mp h'

theorem store_transfer {count slot : Nat} {env : Locals} (hs : slot < count) (hd : Frame.Disposable (env slot))
    (cell : Cell) : Transfers memory (cell :: values count env) (values count (env.set slot (some cell))) := by
  have hclear := (clear_transfer (memory := memory) hs hd).prefix [cell]
  have hstore : Transfers memory (cell :: values count (env.set slot none))
      (values count (env.set slot (some cell))) :=
    Transfers.perm (by simpa only [Option.toList_some, List.singleton_append] using
      (values_set_split count env slot hs (some cell)).symm)
  exact hclear.trans hstore

theorem plain_values {count : Nat} {env : Locals} (hp : ∀ index, Frame.Disposable (env index)) :
    Frame.PlainFields (values count env) := by
  induction count generalizing env with
  | zero => exact .nil
  | succ count ih =>
    have ht := ih (env := tail env) (fun index => hp (index + 1))
    cases hc : env 0 with
    | none => simpa only [values, hc, Option.toList_none, List.nil_append] using ht
    | some cell =>
      have hcell : Frame.Plain cell := by simpa only [hc, Frame.Disposable] using hp 0
      simpa only [values, hc, Option.toList_some, List.singleton_append] using Frame.PlainFields.cons hcell ht

theorem return_transfer {count : Nat} {env : Locals} {cell : Cell} (hs : 0 < count)
    (hc : env 0 = some cell) (hd : ∀ index, index ≠ 0 → Frame.Disposable (env index)) :
    Transfers memory (values count env) [cell] := by
  intro frame h
  have h' := h.perm ((values_move hs hc).append_right frame)
  have hp := plain_values (count := count) (Frame.return_frame_disposable hd)
  obtain ⟨addresses, hf, hn⟩ := h'
  obtain ⟨a, b, rfl, ha, hb⟩ := hf.cons_inv
  obtain ⟨c, d, rfl, hclear, hframe⟩ := fieldsFootprint_split (values count (env.set 0 none)) hb
  have he := hclear.unique (hp.footprint memory)
  subst c
  exact ⟨a ++ d, .cons ha hframe, hn⟩

end SubtreeProofs.Rust.LookupSource.Heap.Spatial
