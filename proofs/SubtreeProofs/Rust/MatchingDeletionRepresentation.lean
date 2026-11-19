module

public import SubtreeProofs.Rust.MatchingDeletionMask
public import SubtreeProofs.Rust.MatchingEntrypoint
public import SubtreeProofs.Shared.MatchingDeletion
import Mathlib.Tactic

/-! # Actual masked matrices denote independent vertex-deleted instances -/

@[expose] public section

open Aeneas Aeneas.Std
open verified_assignment_core

namespace SubtreeProofs.Rust.MatchingDeletionRepresentation

open MatchingDeletionMask MatchingCostSpecification MatchingValidation MatchingEntrypoint MatchingSolveBuiltMatrix

/-- Exact physical contents proved by the actual source mask builder. -/
def Masked (weights : Slice (alloc.vec.Vec (Option I64))) (removed : Usize)
    (masked : alloc.vec.Vec (alloc.vec.Vec (Option I64))) : Prop :=
  masked.val.map alloc.vec.Vec.val = matrixPrefix weights removed.val weights.length

theorem masked_length (weights : Slice (alloc.vec.Vec (Option I64))) (removed : Usize)
    (masked : alloc.vec.Vec (alloc.vec.Vec (Option I64))) (h : Masked weights removed masked) : masked.length = weights.length := by
  have he := congrArg List.length h
  simpa only [matrixPrefix,List.take_length,List.length_map] using he

theorem masked_row (weights : Slice (alloc.vec.Vec (Option I64))) (removed : Usize)
    (masked : alloc.vec.Vec (alloc.vec.Vec (Option I64))) (h : Masked weights removed masked)
    (row : Nat) (hr : row < weights.length) :
    (masked.val[row]!).val = rowPrefix (weights.val[row]!).val removed.val (weights.val[row]!).length := by
  have hl := masked_length weights removed masked h
  have hb : row < masked.val.length := by change row < masked.length; omega
  have he := congrArg (fun rows : List (List (Option I64)) => rows[row]!) h
  simp only [matrixPrefix,List.take_length] at he
  rw [getElem!_pos (masked.val.map alloc.vec.Vec.val) row (by simpa only [List.length_map] using hb),
    getElem!_pos (weights.val.map (fun input => rowPrefix input.val removed.val input.length)) row (by simpa only [List.length_map] using hr),
    List.getElem_map,List.getElem_map] at he
  simpa only [getElem!_pos masked.val row hb,getElem!_pos weights.val row hr] using he

theorem masked_row_length (weights : Slice (alloc.vec.Vec (Option I64))) (removed : Usize)
    (masked : alloc.vec.Vec (alloc.vec.Vec (Option I64))) (h : Masked weights removed masked)
    (row : Nat) (hr : row < weights.length) : (masked.val[row]!).length = (weights.val[row]!).length := by
  have he := congrArg List.length (masked_row weights removed masked h row hr)
  simpa only [rowPrefix_length] using he

theorem masked_cell (weights : Slice (alloc.vec.Vec (Option I64))) (removed : Usize)
    (masked : alloc.vec.Vec (alloc.vec.Vec (Option I64))) (h : Masked weights removed masked)
    (row column : Nat) (hr : row < weights.length) (hc : column < (weights.val[row]!).length) :
    (masked.val[row]!).val[column]! = maskAt (weights.val[row]!).val removed.val column := by
  rw [masked_row weights removed masked h row hr]
  unfold rowPrefix
  rw [getElem!_pos ((List.range (weights.val[row]!).length).map (maskAt (weights.val[row]!).val removed.val)) column
      (by simpa only [List.length_map,List.length_range] using hc),List.getElem_map]
  simp only [List.getElem_range]

/-- Masking changes neither the original width nor its represented machine value. -/
theorem masked_width (weights : Slice (alloc.vec.Vec (Option I64))) (removed : Usize)
    (masked : alloc.vec.Vec (alloc.vec.Vec (Option I64))) (h : Masked weights removed masked) :
    width (alloc.vec.Vec.deref masked) = width weights := by
  have hl := masked_length weights removed masked h
  cases hw : weights.val with
  | nil =>
    have hm : masked.val = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa only [Slice.length,hw,List.length_nil] using hl
    simp only [width,alloc.vec.Vec.deref,Slice.from_val,hm,hw]
  | cons first rest =>
    have hp : 0 < weights.length := by simp only [Slice.length,hw,List.length_cons]; omega
    have he := masked_row_length weights removed masked h 0 hp
    cases hm : masked.val with
    | nil => simp only [alloc.vec.Vec.length,hm,List.length_nil] at hl; omega
    | cons output tail =>
      simp only [hm,hw,List.getElem!_cons_zero] at he
      simp only [width,alloc.vec.Vec.deref,Slice.from_val,hm,hw]
      apply UScalar.eq_of_val_eq
      simpa only [alloc.vec.Vec.len_val] using he

theorem masked_len (weights : Slice (alloc.vec.Vec (Option I64))) (removed : Usize)
    (masked : alloc.vec.Vec (alloc.vec.Vec (Option I64))) (h : Masked weights removed masked) :
    Slice.len (alloc.vec.Vec.deref masked) = Slice.len weights := by
  apply UScalar.eq_of_val_eq
  have hl := masked_length weights removed masked h
  simpa only [Slice.len_val,alloc.vec.Vec.deref,Slice.from_val,Slice.length,alloc.vec.Vec.length] using hl

/-- Every admitted input stays admitted after any column mask. Width and
original indices are retained even when every value in that column is absent. -/
theorem masked_admissible (weights : Slice (alloc.vec.Vec (Option I64))) (removed : Usize)
    (masked : alloc.vec.Vec (alloc.vec.Vec (Option I64))) (h : Masked weights removed masked)
    (ha : Admissible weights) : Admissible (alloc.vec.Vec.deref masked) := by
  have hl := masked_length weights removed masked h
  have hw := masked_width weights removed masked h
  have hlength : (alloc.vec.Vec.deref masked).length = weights.length := by
    simpa only [alloc.vec.Vec.deref,Slice.from_val,Slice.length,alloc.vec.Vec.length] using hl
  refine ⟨?_,?_,?_⟩
  · rw [hw]
    apply (rectangular_iff_index (alloc.vec.Vec.deref masked) (width weights).val).mpr
    intro row hr
    have hp : row < weights.length := by rw [hlength] at hr; exact hr
    have he := masked_row_length weights removed masked h row hp
    have hs := (rectangular_iff_index weights (width weights).val).mp ha.1 row hp
    simpa only [alloc.vec.Vec.deref,Slice.from_val] using he.trans hs
  · rw [hlength,hw]
    exact ha.2.1
  · rw [hlength,hw]
    exact ha.2.2

/-- Concrete input masking agrees exactly with independent right-vertex
removal on optional integer weights, including forbidden and signed entries. -/
theorem masked_model (weights : Slice (alloc.vec.Vec (Option I64))) (removed : Usize)
    (masked : alloc.vec.Vec (alloc.vec.Vec (Option I64))) (h : Masked weights removed masked)
    (left right : Usize) (hl : left.val ≤ weights.length) (hs : Rectangular weights right.val)
    (hr : removed.val < right.val) :
    weightsModel (alloc.vec.Vec.deref masked) left.val right.val =
      WeightedMatching.deleteRight (weightsModel weights left.val right.val) ⟨removed.val,hr⟩ := by
  funext row column
  have hp : row.val < weights.length := row.isLt.trans_le hl
  have hc : column.val < (weights.val[row.val]!).length := by
    rw [(rectangular_iff_index weights right.val).mp hs row.val hp]
    exact column.isLt
  have he := masked_cell weights removed masked h row.val column.val hp hc
  simp only [weightsModel,alloc.vec.Vec.deref,Slice.from_val]
  rw [he]
  simp only [maskAt,WeightedMatching.deleteRight,Fin.ext_iff]
  split
  · simp only [weightValue,↓reduceIte]
  · rfl

end SubtreeProofs.Rust.MatchingDeletionRepresentation

end
