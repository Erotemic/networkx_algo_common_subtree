module

public import SubtreeProofs.Complexity.Memo.Work
public import SubtreeProofs.Complexity.Memo.ProductCache

/-! Primitive work models for the actual list and dense cache operations.
The measures control operation budgets; allocated array length is not asserted
to equal live occupancy, and no machine/source cost realization is assumed. -/

@[expose] public section

namespace SubtreeProofs.Complexity.Memo

namespace ListCache

def workModel [DecidableEq Key] : WorkModel (ops : CacheOps Key Value (List (Key × Value))) where
  size := List.length
  readCost := id
  writeCost := fun _ => 1
  read_mono := fun _ _ h => h
  write_mono := fun _ _ _ => Nat.le_refl _
  read_le := fun key storage _ => read_work_le key storage
  write_le := fun _ _ _ _ _ => Nat.le_refl _
  size_write_le := fun _ _ _ _ _ => Nat.le_refl _

end ListCache

namespace DirectCache

def workModel (capacity : Nat) (Value : Type) : WorkModel (ops capacity Value) where
  size := Array.size
  readCost := fun _ => 1
  writeCost := fun _ => 1
  read_mono := fun _ _ _ => Nat.le_refl _
  write_mono := fun _ _ _ => Nat.le_refl _
  read_le := fun _ _ _ => Nat.le_refl _
  write_le := fun _ _ _ _ _ => Nat.le_refl _
  size_write_le := by
    intro key value storage _ _
    simp only [ops, Array.size_setIfInBounds]
    exact Nat.le_succ _

def productWorkModel (rows columns : Nat) (Value : Type) :
    WorkModel (productOps rows columns Value) where
  size := Array.size
  readCost := fun _ => 3
  writeCost := fun _ => 3
  read_mono := fun _ _ _ => Nat.le_refl _
  write_mono := fun _ _ _ => Nat.le_refl _
  read_le := fun _ _ _ => Nat.le_refl _
  write_le := fun _ _ _ _ _ => Nat.le_refl _
  size_write_le := by
    intro key value storage _ _
    simp only [productOps, ops, Array.size_setIfInBounds]
    exact Nat.le_succ _

end DirectCache
end SubtreeProofs.Complexity.Memo
