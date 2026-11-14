module

public import SubtreeProofs.Rust.MatchingDeletionCorrectness
import Mathlib.Tactic

/-! # Independent indexed correctness invariant of the actual deletion family -/

@[expose] public section

open Aeneas Aeneas.Std
open verified_assignment_core

namespace SubtreeProofs.Rust.MatchingDeletionInvariant

open MatchingCostSpecification MatchingEntrypoint MatchingSolveBuiltMatrix MatchingDecoding

instance : Inhabited matching.PartialMatching := ⟨⟨alloc.vec.Vec.new matching.MatchedPair,0#i128⟩⟩

def CorrectDeleted (weights : Slice (alloc.vec.Vec (Option I64))) (removed : Fin (width weights).val)
    (result : matching.PartialMatching) : Prop :=
  CorrectFor (Slice.len weights) (width weights)
    (WeightedMatching.deleteRight (weightsModel weights (Slice.len weights).val (width weights).val) removed) result

def Unused (original : matching.PartialMatching) (column : Nat) : Prop :=
  ∀ pair ∈ original.pairs.val, pair.right.val ≠ column

structure Invariant (weights : Slice (alloc.vec.Vec (Option I64))) (original : matching.PartialMatching)
    (results : alloc.vec.Vec matching.PartialMatching) (removed : Usize) : Prop where
  bound : removed.val ≤ (width weights).val
  length : results.length = removed.val
  correct : ∀ column : Fin (width weights).val, column.val < removed.val → CorrectDeleted weights column results.val[column.val]!
  copied : ∀ column : Fin (width weights).val, column.val < removed.val → Unused original column.val → results.val[column.val]! = original

def CorrectFamily (weights : Slice (alloc.vec.Vec (Option I64))) (family : deletion.DeletionFamily) : Prop :=
  CorrectPartial weights (Slice.len weights) (width weights) family.original ∧
    Invariant weights family.original family.without_right (width weights)

/-- Appending a genuinely correct next deleted instance preserves every
previous result and the exact physical reuse of unmatched solutions. -/
theorem append_invariant (weights : Slice (alloc.vec.Vec (Option I64))) (original : matching.PartialMatching)
    (results after : alloc.vec.Vec matching.PartialMatching) (removed next : Usize) (result : matching.PartialMatching)
    (h : Invariant weights original results removed) (hr : removed.val < (width weights).val)
    (hafter : after.val = results.val ++ [result]) (hnext : next.val = removed.val+1)
    (hc : CorrectDeleted weights ⟨removed.val,hr⟩ result)
    (hcopy : Unused original removed.val → result = original) : Invariant weights original after next := by
  have hlen : results.val.length = removed.val := h.length
  have hlast : after.val[removed.val]! = result := by
    rw [hafter,List.getElem!_append_right results.val [result] removed.val (by rw [hlen])]
    simp only [hlen,Nat.sub_self,List.getElem!_cons_zero]
  have hold : ∀ index < removed.val, after.val[index]! = results.val[index]! := by
    intro index hi
    rw [hafter,List.getElem!_append_left results.val [result] index (by rw [hlen]; exact hi)]
  refine ⟨by omega,?_,?_,?_⟩
  · change after.val.length = next.val
    rw [hafter,List.length_append,List.length_singleton,hlen,hnext]
  · intro column hcol
    by_cases hp : column.val < removed.val
    · rw [hold column.val hp]
      exact h.correct column hp
    · have he : column = ⟨removed.val,hr⟩ := Fin.ext (by change column.val = removed.val; omega)
      subst column
      rw [hlast]
      exact hc
  · intro column hcol hunused
    by_cases hp : column.val < removed.val
    · rw [hold column.val hp]
      exact h.copied column hp hunused
    · have he : column.val = removed.val := by omega
      rw [he,hlast]
      exact hcopy (by simpa only [he] using hunused)

end SubtreeProofs.Rust.MatchingDeletionInvariant

end
