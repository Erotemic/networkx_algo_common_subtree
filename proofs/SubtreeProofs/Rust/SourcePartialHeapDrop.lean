module

public import SubtreeProofs.Rust.SourcePartialHeap

/-! Logical addressed destruction traverses stored Box pointers under the
initialization mask, retaining exact owner identities and declared drop work.
Allocation liveness is an explicit resource; shared-loan protection and actual
Rust glue/allocator interpretation remain separate obligations. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open LookupSource.Heap

mutual
  def destroy (memory : Memory) (cell : Cell) : (part : Slot) → Option (List Nat × DropWork)
    | .empty => some ([], {})
    | .boolean _ => match cell with
      | .boolean _ => some ([], ⟨1, 0⟩)
      | _ => none
    | .number _ => match cell with
      | .number _ => some ([], ⟨1, 0⟩)
      | _ => none
    | .shared _ => match cell with
      | .shared _ => some ([], ⟨1, 0⟩)
      | _ => none
    | .node kind variant parts => match cell with
      | .node actual tag cells => do
        if kind == actual && variant == tag then
          let (owners, work) ← destroyFields memory cells parts
          some (owners, (⟨1, 0⟩ : DropWork).plus work)
        else none
      | _ => none
    | .boxed part => match cell with
      | .owned address => do
        let child ← memory[address]?
        let (owners, work) ← destroy memory child part
        some (owners ++ [address], (⟨1, 1⟩ : DropWork).plus work)
      | _ => none
  termination_by part => sizeOf part

  def destroyFields (memory : Memory) : List Cell → (parts : List Slot) → Option (List Nat × DropWork)
    | [], [] => some ([], {})
    | cell :: cells, part :: parts => do
      let (first, a) ← destroy memory cell part
      let (rest, b) ← destroyFields memory cells parts
      some (first ++ rest, a.plus b)
    | _, _ => none
  termination_by _ parts => sizeOf parts
end

mutual
  theorem Rep.destroy {memory : Memory} {cell : Cell} {part : Slot} {owners : List Nat}
      (h : Rep memory cell part owners) : destroy memory cell part = some (owners, part.dropWork) := by
    cases h with
    | empty _ | boolean _ | number _ | shared _ => simp only [destroy, Slot.dropWork]
    | node fields =>
      simp only [destroy, beq_self_eq_true, Bool.and_true, ite_true, fields.destroy,
        bind, Option.bind, Slot.dropWork]
    | owned hr child => simp only [destroy, hr, child.destroy, bind, Option.bind, Slot.dropWork]

  theorem FieldsRep.destroy {memory : Memory} {cells : List Cell} {parts : List Slot} {owners : List Nat}
      (h : FieldsRep memory cells parts owners) : destroyFields memory cells parts = some (owners, dropFields parts) := by
    cases h with
    | nil => simp only [destroyFields, dropFields]
    | cons first rest => simp only [destroyFields, first.destroy, rest.destroy, bind, Option.bind, dropFields]
end

theorem Rep.unique {memory : Memory} {cell : Cell} {part : Slot} {first second : List Nat}
    (hfirst : Rep memory cell part first) (hsecond : Rep memory cell part second) : first = second :=
  congrArg Prod.fst (Option.some.inj (hfirst.destroy.symm.trans hsecond.destroy))

theorem destroy_full_owned {memory : Memory} {cell : Cell} {value : Value} {start stop : Nat}
    (hr : Represents memory cell value) (ho : Owns memory cell start stop) :
    destroy memory cell (Slot.ofValue value) =
      some (List.range' start (stop - start), (Slot.ofValue value).dropWork) :=
  (Rep.of_full hr ho.footprint).destroy

open verified_ordered_core in
theorem destroy_packed_word (word : BalancedWord) (memory : Memory) :
    destroy (packWord word memory).2 (packWord word memory).1 (Slot.ofValue (encodeWord word)) =
      some (List.range' memory.length ((packWord word memory).2.length - memory.length),
        (Slot.ofValue (encodeWord word)).dropWork) :=
  destroy_full_owned (packWord_spec word memory).1 (packWord_owns word memory)

open verified_ordered_core in
theorem destroy_packed_result (value : CommonEmbedding) (memory : Memory) :
    destroy (packResult value memory).2 (packResult value memory).1 (Slot.ofValue (encodeResult value)) =
      some (List.range' memory.length ((packResult value memory).2.length - memory.length),
        (Slot.ofValue (encodeResult value)).dropWork) :=
  destroy_full_owned (packResult_spec value memory).1 (packResult_owns value memory)

abbrev Live := Nat → Bool

def AliveOn (live : Live) (owners : List Nat) : Prop := ∀ address ∈ owners, live address = true

def retire (live : Live) (owners : List Nat) : Live := fun address =>
  if address ∈ owners then false else live address

theorem retire_member (live : Live) {owners : List Nat} {address : Nat} (h : address ∈ owners) :
    retire live owners address = false := by simp only [retire, h, ite_true]

theorem retire_other (live : Live) {owners : List Nat} {address : Nat} (h : address ∉ owners) :
    retire live owners address = live address := by simp only [retire, h, ite_false]

theorem retire_preserves {live : Live} {owners guarded : List Nat}
    (hs : ∀ address ∈ guarded, address ∉ owners) (hl : AliveOn live guarded) :
    AliveOn (retire live owners) guarded := by
  intro address ha
  rw [retire_other live (hs address ha)]
  exact hl address ha

theorem retired_not_alive (live : Live) {owners : List Nat} (hn : owners ≠ []) :
    ¬ AliveOn (retire live owners) owners := by
  intro ha
  cases owners with
  | nil => exact hn rfl
  | cons address rest =>
    have hb := ha address (by simp)
    rw [retire_member live (by simp)] at hb
    cases hb

/-- Retirement consumes live, duplicate-free owner identities while preserving
an explicitly guarded address list. Protection may contain shared aliases. -/
theorem Rep.destroy_retire {memory : Memory} {cell : Cell} {part : Slot} {owners : List Nat}
    (h : Rep memory cell part owners) {live : Live} (hl : AliveOn live owners) (hn : owners.Nodup)
    {guarded : List Nat} (hs : ∀ address ∈ guarded, address ∉ owners) (hp : AliveOn live guarded) :
    Addressed.destroy memory cell part = some (owners, part.dropWork) ∧
      owners.length = part.dropWork.boxes ∧ owners.Nodup ∧
      (∀ address ∈ owners, live address = true ∧ retire live owners address = false) ∧
      AliveOn (retire live owners) guarded :=
  ⟨h.destroy, h.boxes, hn, fun address ha => ⟨hl address ha, retire_member live ha⟩, retire_preserves hs hp⟩

end SubtreeProofs.Rust.LookupSource.Partial.Addressed
