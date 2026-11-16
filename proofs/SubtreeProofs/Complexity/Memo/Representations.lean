module

public import SubtreeProofs.Complexity.Memo.Interpreter
public import Mathlib.Data.List.Basic

/-!
# Counted list and direct-address cache representations

The list currency counts whole-key equality tests. The array currency counts
bounded array-word reads, writes and initialization pushes. These explicit
primitive models are not structural-key, persistent-copy, bit-operation or
Rust allocator runtime theorems. Concrete source applications still need their
primitive/source realization and key-conversion costs.
-/

@[expose] public section

namespace SubtreeProofs.Complexity.Memo
namespace ListCache

/-- The counter is accumulated by the actual first-hit scan. -/
def read [DecidableEq Key] (key : Key) : List (Key × Value) → Option Value × Nat
  | [] => (none, 0)
  | (stored, value) :: rest =>
    if key = stored then (some value, 1) else
      let result := read key rest
      (result.1, result.2 + 1)

theorem read_value [DecidableEq Key] (key : Key) (storage : List (Key × Value)) :
    (read key storage).1 = storage.lookup key := by
  induction storage with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨stored, value⟩
    by_cases he : key = stored
    · simp [read, List.lookup, he]
    · simp [read, he, List.lookup, beq_false_of_ne he, ih]

theorem read_work_le [DecidableEq Key] (key : Key) (storage : List (Key × Value)) :
    (read key storage).2 ≤ storage.length := by
  induction storage with
  | nil => simp [read]
  | cons entry rest ih =>
    rcases entry with ⟨stored, value⟩
    simp only [read]
    split <;> simp only [List.length_cons] <;> omega

/-- Relate the standard lookup API to this representation's key list. -/
theorem lookup_none_iff [DecidableEq Key] (key : Key) (storage : List (Key × Value)) :
    storage.lookup key = none ↔ key ∉ storage.map Prod.fst := by
  induction storage with
  | nil => simp
  | cons entry rest ih =>
    rcases entry with ⟨stored, value⟩
    by_cases he : key = stored
    · simp [List.lookup, he]
    · simp only [List.lookup, beq_false_of_ne he, List.map_cons, List.mem_cons, he, false_or]
      exact ih

def ops [DecidableEq Key] : CacheOps Key Value (List (Key × Value)) where
  contents := fun storage key => storage.lookup key
  Valid := fun storage => (storage.map Prod.fst).Nodup
  read := read
  write := fun key value storage => ((key, value) :: storage, 1)
  read_correct := fun key storage _ => read_value key storage
  write_valid := by
    intro key value storage hv hf
    exact List.nodup_cons.mpr ⟨(lookup_none_iff key storage).mp hf, hv⟩
  write_same := by
    intro key value storage _
    simp [List.lookup]
  write_other := by
    intro key value storage other _ hne
    simp only [List.lookup, beq_false_of_ne hne]

def buildEmpty : List (Key × Value) × Nat := ([], 1)

theorem initial_valid [DecidableEq Key] :
    (ops : CacheOps Key Value _).Valid (buildEmpty : List (Key × Value) × Nat).1 := by simp [ops, buildEmpty]

theorem initial_sound [DecidableEq Key] (answer : Key → Value) :
    (ops : CacheOps Key Value _).Sound answer (buildEmpty : List (Key × Value) × Nat).1 := by
  intro key value hv
  simp [ops, buildEmpty] at hv

end ListCache

namespace DirectCache

/-- Build every cell explicitly. The setup count includes one empty-array
construction and one push per cell; initialization is not free. -/
def buildEmpty (Value : Type) : Nat → Array (Option Value) × Nat
  | 0 => (#[], 1)
  | size + 1 =>
    let previous := buildEmpty Value size
    (previous.1.push none, previous.2 + 1)

@[simp] theorem buildEmpty_size (Value : Type) (size : Nat) :
    (buildEmpty Value size).1.size = size := by
  induction size with
  | zero => rfl
  | succ size ih => simp [buildEmpty, ih]

@[simp] theorem buildEmpty_work (Value : Type) (size : Nat) :
    (buildEmpty Value size).2 = size + 1 := by
  induction size with
  | zero => rfl
  | succ size ih => simp [buildEmpty, ih]

theorem buildEmpty_empty (Value : Type) (size index : Nat) :
    ((buildEmpty Value size).1[index]?).getD none = none := by
  induction size with
  | zero => rfl
  | succ size ih =>
    change ((buildEmpty Value size).1.push none)[index]?.getD none = none
    rw [Array.getElem?_push]
    split
    · rfl
    · exact ih

/-- Keys carry their dense bound. No unchecked raw-key-to-index map is a field
of this implementation; clients must construct and account for that map. -/
def ops (capacity : Nat) (Value : Type) : CacheOps (Fin capacity) Value (Array (Option Value)) where
  contents := fun storage key => (storage[key.val]?).getD none
  Valid := fun storage => storage.size = capacity
  read := fun key storage => ((storage[key.val]?).getD none, 1)
  write := fun key value storage => (storage.setIfInBounds key.val (some value), 1)
  read_correct := fun _ _ _ => rfl
  write_valid := by
    intro key value storage hv _
    simpa only [Array.size_setIfInBounds] using hv
  write_same := by
    intro key value storage hv
    have hi : key.val < storage.size := by rw [hv]; exact key.isLt
    change ((storage.setIfInBounds key.val (some value))[key.val]?).getD none = some value
    rw [Array.getElem?_setIfInBounds_self_of_lt hi]
    rfl
  write_other := by
    intro key value storage other _ hne
    have hi : key.val ≠ other.val := fun he => hne (Fin.ext he.symm)
    change ((storage.setIfInBounds key.val (some value))[other.val]?).getD none = _
    rw [Array.getElem?_setIfInBounds_ne hi]

theorem initial_valid (capacity : Nat) (Value : Type) :
    (ops capacity Value).Valid (buildEmpty Value capacity).1 := buildEmpty_size Value capacity

theorem initial_sound (capacity : Nat) (Value : Type) (answer : Fin capacity → Value) :
    (ops capacity Value).Sound answer (buildEmpty Value capacity).1 := by
  intro key value hv
  change ((buildEmpty Value capacity).1[key.val]?).getD none = some value at hv
  rw [buildEmpty_empty] at hv
  cases hv

@[simp] theorem read_work (capacity : Nat) (Value : Type) (key : Fin capacity)
    (storage : Array (Option Value)) : ((ops capacity Value).read key storage).2 = 1 := rfl

@[simp] theorem write_work (capacity : Nat) (Value : Type) (key : Fin capacity) (value : Value)
    (storage : Array (Option Value)) : ((ops capacity Value).write key value storage).2 = 1 := rfl

end DirectCache
end SubtreeProofs.Complexity.Memo
