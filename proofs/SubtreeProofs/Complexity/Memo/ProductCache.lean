module

public import SubtreeProofs.Complexity.Memo.Representations
public import Mathlib.Logic.Equiv.Fin.Basic

/-! Direct addressing for bounded index pairs, using Mathlib's checked dense
equivalence. Every read/write adds two declared arithmetic units for the
actual `column + width * row` encoding. The currency is bounded-word arithmetic
and cell access, not Nat bit complexity, persistent-array copying or Rust cost. -/

@[expose] public section

namespace SubtreeProofs.Complexity.Memo.DirectCache

def productOps (rows columns : Nat) (Value : Type) :
    CacheOps (Fin rows × Fin columns) Value (Array (Option Value)) where
  contents := fun storage key => (ops (rows * columns) Value).contents storage (finProdFinEquiv key)
  Valid := (ops (rows * columns) Value).Valid
  read := fun key storage =>
    let encoded := finProdFinEquiv key
    let result := (ops (rows * columns) Value).read encoded storage
    (result.1, result.2 + 2)
  write := fun key value storage =>
    let encoded := finProdFinEquiv key
    let result := (ops (rows * columns) Value).write encoded value storage
    (result.1, result.2 + 2)
  read_correct := fun key storage hv =>
    (ops (rows * columns) Value).read_correct (finProdFinEquiv key) storage hv
  write_valid := fun key value storage hv hf =>
    (ops (rows * columns) Value).write_valid (finProdFinEquiv key) value storage hv hf
  write_same := fun key value storage hv =>
    (ops (rows * columns) Value).write_same (finProdFinEquiv key) value storage hv
  write_other := by
    intro key value storage other hv hne
    exact (ops (rows * columns) Value).write_other (finProdFinEquiv key) value storage
      (finProdFinEquiv other) hv (fun he => hne (finProdFinEquiv.injective he))

theorem product_initial_valid (rows columns : Nat) (Value : Type) :
    (productOps rows columns Value).Valid (buildEmpty Value (rows * columns)).1 :=
  initial_valid (rows * columns) Value

theorem product_initial_sound (rows columns : Nat) (Value : Type)
    (answer : Fin rows × Fin columns → Value) :
    (productOps rows columns Value).Sound answer (buildEmpty Value (rows * columns)).1 := by
  intro key value hv
  change ((buildEmpty Value (rows * columns)).1[(finProdFinEquiv key).val]?).getD none =
    some value at hv
  rw [buildEmpty_empty] at hv
  cases hv

@[simp] theorem product_read_work (rows columns : Nat) (Value : Type)
    (key : Fin rows × Fin columns) (storage : Array (Option Value)) :
    ((productOps rows columns Value).read key storage).2 = 3 := rfl

@[simp] theorem product_write_work (rows columns : Nat) (Value : Type)
    (key : Fin rows × Fin columns) (value : Value) (storage : Array (Option Value)) :
    ((productOps rows columns Value).write key value storage).2 = 3 := rfl

end SubtreeProofs.Complexity.Memo.DirectCache
